use ff::{Field, FromUniformBytes, PrimeField};
use pasta_curves::arithmetic::CurveExt;
use static_assertions::const_assert;
use subtle::{ConditionallySelectable, ConstantTimeEq};

/// Hashes over a message and writes the output to all of `buf`.
/// Modified from https://github.com/zcash/pasta_curves/blob/7e3fc6a4919f6462a32b79dd226cb2587b7961eb/src/hashtocurve.rs#L11.
fn hash_to_field<F: FromUniformBytes<64>>(
    method: &str,
    curve_id: &str,
    domain_prefix: &str,
    message: &[u8],
    buf: &mut [F; 2],
) {
    assert!(domain_prefix.len() < 256);
    assert!((18 + method.len() + curve_id.len() + domain_prefix.len()) < 256);

    // Assume that the field size is 32 bytes and k is 256, where k is defined in
    // <https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html#name-security-considerations-3>.
    const CHUNKLEN: usize = 64;
    const_assert!(CHUNKLEN * 2 < 256);

    // Input block size of BLAKE2b.
    const R_IN_BYTES: usize = 128;

    let personal = [0u8; 16];
    let empty_hasher = blake2b_simd::Params::new()
        .hash_length(CHUNKLEN)
        .personal(&personal)
        .to_state();

    let b_0 = empty_hasher
        .clone()
        .update(&[0; R_IN_BYTES])
        .update(message)
        .update(&[0, (CHUNKLEN * 2) as u8, 0])
        .update(domain_prefix.as_bytes())
        .update(b"-")
        .update(curve_id.as_bytes())
        .update(b"_XMD:BLAKE2b_")
        .update(method.as_bytes())
        .update(b"_RO_")
        .update(&[(18 + method.len() + curve_id.len() + domain_prefix.len()) as u8])
        .finalize();

    let b_1 = empty_hasher
        .clone()
        .update(b_0.as_array())
        .update(&[1])
        .update(domain_prefix.as_bytes())
        .update(b"-")
        .update(curve_id.as_bytes())
        .update(b"_XMD:BLAKE2b_")
        .update(method.as_bytes())
        .update(b"_RO_")
        .update(&[(18 + method.len() + curve_id.len() + domain_prefix.len()) as u8])
        .finalize();

    let b_2 = {
        let mut empty_hasher = empty_hasher;
        for (l, r) in b_0.as_array().iter().zip(b_1.as_array().iter()) {
            empty_hasher.update(&[*l ^ *r]);
        }
        empty_hasher
            .update(&[2])
            .update(domain_prefix.as_bytes())
            .update(b"-")
            .update(curve_id.as_bytes())
            .update(b"_XMD:BLAKE2b_")
            .update(method.as_bytes())
            .update(b"_RO_")
            .update(&[(18 + method.len() + curve_id.len() + domain_prefix.len()) as u8])
            .finalize()
    };

    for (big, buf) in [b_1, b_2].iter().zip(buf.iter_mut()) {
        let mut little = [0u8; CHUNKLEN];
        little.copy_from_slice(big.as_array());
        little.reverse();
        *buf = F::from_uniform_bytes(&little);
    }
}

/// Implementation of https://www.ietf.org/id/draft-irtf-cfrg-hash-to-curve-16.html#name-shallue-van-de-woestijne-met
#[allow(clippy::type_complexity)]
pub(crate) fn svdw_map_to_curve<'a, C>(
    curve_id: &'static str,
    domain_prefix: &'a str,
    z: C::Base,
) -> Box<dyn Fn(&[u8]) -> C + 'a>
where
    C: CurveExt,
    C::Base: FromUniformBytes<64>,
{
    let one = C::Base::ONE;
    let three = one + one + one;
    let four = three + one;
    let a = C::a();
    let b = C::b();
    let tmp = three * z.square() + four * a;

    // Precomputed constants:
    // 1. c1 = g(Z)
    let c1 = (z.square() + a) * z + b;
    // 2. c2 = -Z / 2
    let c2 = -z * C::Base::TWO_INV;
    // 3. c3 = sqrt(-g(Z) * (3 * Z^2 + 4 * A))    # sgn0(c3) MUST equal 0
    let c3 = {
        let c3 = (-c1 * tmp).sqrt().unwrap();
        C::Base::conditional_select(&c3, &-c3, c3.is_odd())
    };
    // 4. c4 = -4 * g(Z) / (3 * Z^2 + 4 * A)
    let c4 = -four * c1 * tmp.invert().unwrap();

    Box::new(move |message| {
        let mut us = [C::Base::ZERO; 2];
        hash_to_field("SVDW", curve_id, domain_prefix, message, &mut us);

        let [q0, q1] = us.map(|u| {
            // 1. tv1 = u^2
            let tv1 = u.square();
            // 2. tv1 = tv1 * c1
            let tv1 = tv1 * c1;
            // 3. tv2 = 1 + tv1
            let tv2 = one + tv1;
            // 4. tv1 = 1 - tv1
            let tv1 = one - tv1;
            // 5. tv3 = tv1 * tv2
            let tv3 = tv1 * tv2;
            // 6. tv3 = inv0(tv3)
            let tv3 = tv3.invert().unwrap_or(C::Base::ZERO);
            // 7. tv4 = u * tv1
            let tv4 = u * tv1;
            // 8. tv4 = tv4 * tv3
            let tv4 = tv4 * tv3;
            // 9. tv4 = tv4 * c3
            let tv4 = tv4 * c3;
            // 10. x1 = c2 - tv4
            let x1 = c2 - tv4;
            // 11. gx1 = x1^2
            let gx1 = x1.square();
            // 12. gx1 = gx1 + A
            let gx1 = gx1 + a;
            // 13. gx1 = gx1 * x1
            let gx1 = gx1 * x1;
            // 14. gx1 = gx1 + B
            let gx1 = gx1 + b;
            // 15. e1 = is_square(gx1)
            let e1 = gx1.sqrt().is_some();
            // 16. x2 = c2 + tv4
            let x2 = c2 + tv4;
            // 17. gx2 = x2^2
            let gx2 = x2.square();
            // 18. gx2 = gx2 + A
            let gx2 = gx2 + a;
            // 19. gx2 = gx2 * x2
            let gx2 = gx2 * x2;
            // 20. gx2 = gx2 + B
            let gx2 = gx2 + b;
            // 21. e2 = is_square(gx2) AND NOT e1    # Avoid short-circuit logic ops
            let e2 = gx2.sqrt().is_some() & (!e1);
            // 22. x3 = tv2^2
            let x3 = tv2.square();
            // 23. x3 = x3 * tv3
            let x3 = x3 * tv3;
            // 24. x3 = x3^2
            let x3 = x3.square();
            // 25. x3 = x3 * c4
            let x3 = x3 * c4;
            // 26. x3 = x3 + Z
            let x3 = x3 + z;
            // 27. x = CMOV(x3, x1, e1)    # x = x1 if gx1 is square, else x = x3
            let x = C::Base::conditional_select(&x3, &x1, e1);
            // 28. x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
            let x = C::Base::conditional_select(&x, &x2, e2);
            // 29. gx = x^2
            let gx = x.square();
            // 30. gx = gx + A
            let gx = gx + a;
            // 31. gx = gx * x
            let gx = gx * x;
            // 32. gx = gx + B
            let gx = gx + b;
            // 33. y = sqrt(gx)
            let y = gx.sqrt().unwrap();
            // 34. e3 = sgn0(u) == sgn0(y)
            let e3 = u.is_odd().ct_eq(&y.is_odd());
            // 35. y = CMOV(-y, y, e3)    # Select correct sign of y
            let y = C::Base::conditional_select(&-y, &y, e3);
            // 36. return (x, y)
            C::new_jacobian(x, y, one).unwrap()
        });

        let r = q0 + &q1;
        debug_assert!(bool::from(r.is_on_curve()));
        r
    })
}

/// Implements a degree 3 isogeny map.
/// Copy from https://github.com/zcash/pasta_curves/blob/7e3fc6a4919f6462a32b79dd226cb2587b7961eb/src/hashtocurve.rs#L81
fn degree_3_iso_map<C: CurveExt>(p: &C, iso: &[C::Base; 13]) -> C {
    // The input and output are in Jacobian coordinates, using the method
    // in "Avoiding inversions" [WB2019, section 4.3].

    let (x, y, z) = p.jacobian_coordinates();

    let z2 = z.square();
    let z3 = z2 * z;
    let z4 = z2.square();
    let z6 = z3.square();

    let num_x = ((iso[0] * x + iso[1] * z2) * x + iso[2] * z4) * x + iso[3] * z6;
    let div_x = (z2 * x + iso[4] * z4) * x + iso[5] * z6;

    let num_y = (((iso[6] * x + iso[7] * z2) * x + iso[8] * z4) * x + iso[9] * z6) * y;
    let div_y = (((x + iso[10] * z2) * x + iso[11] * z4) * x + iso[12] * z6) * z3;

    let zo = div_x * div_y;
    let xo = num_x * div_y * zo;
    let yo = num_y * div_x * zo.square();

    C::new_jacobian(xo, yo, zo).unwrap()
}

/// Implementation of https://www.ietf.org/id/draft-irtf-cfrg-hash-to-curve-16.html#name-simplified-swu-for-ab-0 with degree 3 isogeny.
/// Modified from https://github.com/zcash/pasta_curves/blob/7e3fc6a4919f6462a32b79dd226cb2587b7961eb/src/hashtocurve.rs#L109
#[allow(clippy::type_complexity)]
pub(crate) fn degree_3_sswu_map_to_curve<'a, C>(
    curve_id: &'static str,
    domain_prefix: &'a str,
    z: C::Base,
    theta: C::Base,
    isogeny_constants: [C::Base; 13],
) -> Box<dyn Fn(&[u8]) -> C + 'a>
where
    C: CurveExt,
    C::Base: FromUniformBytes<64>,
{
    Box::new(move |message| {
        let mut us = [C::Base::ZERO; 2];
        hash_to_field("SSWU", curve_id, domain_prefix, message, &mut us);

        let [q0, q1] = us.map(|u| {
            // 1. tv1 = inv0(Z^2 * u^4 + Z * u^2)
            // 2. x1 = (-B / A) * (1 + tv1)
            // 3. If tv1 == 0, set x1 = B / (Z * A)
            // 4. gx1 = x1^3 + A * x1 + B
            //
            // We use the "Avoiding inversions" optimization in [WB2019, section 4.2]
            // (not to be confused with section 4.3):
            //
            //   here       [WB2019]
            //   -------    ---------------------------------
            //   Z          ξ
            //   u          t
            //   Z * u^2    ξ * t^2 (called u, confusingly)
            //   x1         X_0(t)
            //   x2         X_1(t)
            //   gx1        g(X_0(t))
            //   gx2        g(X_1(t))
            //
            // Using the "here" names:
            //    x1 = num_x1/div      = [B*(Z^2 * u^4 + Z * u^2 + 1)] / [-A*(Z^2 * u^4 + Z * u^2]
            //   gx1 = num_gx1/div_gx1 = [num_x1^3 + A * num_x1 * div^2 + B * div^3] / div^3

            let a = C::a();
            let b = C::b();
            let z_u2 = z * u.square();
            let ta = z_u2.square() + z_u2;
            let num_x1 = b * (ta + C::Base::ONE);
            let div = a * C::Base::conditional_select(&-ta, &z, ta.is_zero());
            let num2_x1 = num_x1.square();
            let div2 = div.square();
            let div3 = div2 * div;
            let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;

            // 5. x2 = Z * u^2 * x1
            let num_x2 = z_u2 * num_x1; // same div

            // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
            // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
            // 8. Else set x = x2 and y = sqrt(gx2)
            let (gx1_square, y1) = C::Base::sqrt_ratio(&num_gx1, &div3);

            // This magic also comes from a generalization of [WB2019, section 4.2].
            //
            // The Sarkar square root algorithm with input s gives us a square root of
            // h * s for free when s is not square, where h is a fixed nonsquare.
            // In our implementation, h = ROOT_OF_UNITY.
            // We know that Z / h is a square since both Z and h are
            // nonsquares. Precompute theta as a square root of Z / ROOT_OF_UNITY.
            //
            // We have gx2 = g(Z * u^2 * x1) = Z^3 * u^6 * gx1
            //                               = (Z * u^3)^2 * (Z/h * h * gx1)
            //                               = (Z * theta * u^3)^2 * (h * gx1)
            //
            // When gx1 is not square, y1 is a square root of h * gx1, and so Z * theta * u^3 * y1
            // is a square root of gx2. Note that we don't actually need to compute gx2.

            let y2 = theta * z_u2 * u * y1;
            let num_x = C::Base::conditional_select(&num_x2, &num_x1, gx1_square);
            let y = C::Base::conditional_select(&y2, &y1, gx1_square);

            // 9. If sgn0(u) != sgn0(y), set y = -y
            let y = C::Base::conditional_select(&(-y), &y, u.is_odd().ct_eq(&y.is_odd()));

            C::new_jacobian(num_x * div, y * div3, div).unwrap()
        });

        let r = q0 + &q1;
        debug_assert!(bool::from(r.is_on_curve()));
        degree_3_iso_map(&r, &isogeny_constants)
    })
}
