use crate::ff::WithSmallOrderMulGroup;
use crate::ff::{Field, PrimeField};
use crate::group::{prime::PrimeCurveAffine, Curve, Group as _, GroupEncoding};
use crate::hash_to_curve::degree_3_sswu_map_to_curve;
use crate::secp256k1::Fp;
use crate::secp256k1::Fq;
use crate::{Coordinates, CurveAffine, CurveAffineExt, CurveExt};
use core::cmp;
use core::fmt::Debug;
use core::iter::Sum;
use core::ops::{Add, Mul, Neg, Sub};
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "derive_serde")]
use serde::{Deserialize, Serialize};

impl group::cofactor::CofactorGroup for Secp256k1 {
    type Subgroup = Secp256k1;

    fn clear_cofactor(&self) -> Self {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, 1.into())
    }

    fn is_torsion_free(&self) -> Choice {
        1.into()
    }
}

// Reference: https://neuromancer.sk/std/secg/secp256k1
const SECP_GENERATOR_X: Fp = Fp::from_raw([
    0x59F2815B16F81798,
    0x029BFCDB2DCE28D9,
    0x55A06295CE870B07,
    0x79BE667EF9DCBBAC,
]);
const SECP_GENERATOR_Y: Fp = Fp::from_raw([
    0x9C47D08FFB10D4B8,
    0xFD17B448A6855419,
    0x5DA4FBFC0E1108A8,
    0x483ADA7726A3C465,
]);
const SECP_B: Fp = Fp::from_raw([7, 0, 0, 0]);

use crate::{
    batch_add, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, new_curve_impl,
};

new_curve_impl!(
    (pub),
    Secp256k1,
    Secp256k1Affine,
    true,
    Fp,
    Fq,
    (SECP_GENERATOR_X,SECP_GENERATOR_Y),
    SECP_B,
    "secp256k1",
    |curve_id, domain_prefix| degree_3_sswu_map_to_curve(curve_id, domain_prefix, Secp256k1::Z, Secp256k1::THETA, Secp256k1::ISOGENY_CONSTANTS),
);

impl Secp256k1 {
    /// Constants used for computing the degree 3 isogeny map.
    /// Taken from https://www.ietf.org/id/draft-irtf-cfrg-hash-to-curve-16.html#appx-iso-secp256k1.
    pub const ISOGENY_CONSTANTS: [Fp; 13] = [
        Fp::from_raw([
            0x8e38e38daaaaa88c,
            0x38e38e38e38e38e3,
            0xe38e38e38e38e38e,
            0x8e38e38e38e38e38,
        ]),
        Fp::from_raw([
            0x4ecbd0b53d9dd262,
            0xe4506144037c4031,
            0xe2a413deca25caec,
            0x534c328d23f234e6,
        ]),
        Fp::from_raw([
            0xdfff1044f17c6581,
            0xd595d2fc0bf63b92,
            0xb9f315cea7fd44c5,
            0x07d3d4c80bc321d5,
        ]),
        Fp::from_raw([
            0x8e38e38daaaaa8c7,
            0x38e38e38e38e38e3,
            0xe38e38e38e38e38e,
            0x8e38e38e38e38e38,
        ]),
        Fp::from_raw([
            0xc52a56612a8c6d14,
            0x06d36b641f5e41bb,
            0xf7c4b2d51b542254,
            0xedadc6f64383dc1d,
        ]),
        Fp::from_raw([
            0x9fe6b745781eb49b,
            0x86cd409542f8487d,
            0x9ca34ccbb7b640dd,
            0xd35771193d94918a,
        ]),
        Fp::from_raw([
            0x84bda12f38e38d84,
            0xbda12f684bda12f6,
            0xa12f684bda12f684,
            0x2f684bda12f684bd,
        ]),
        Fp::from_raw([
            0xa765e85a9ecee931,
            0x722830a201be2018,
            0x715209ef6512e576,
            0x29a6194691f91a73,
        ]),
        Fp::from_raw([
            0xdffc90fc201d71a3,
            0x647ab046d686da6f,
            0xa9d0a54b12a0a6d5,
            0xc75e0c32d5cb7c0f,
        ]),
        Fp::from_raw([
            0xa12f684b8e38e23c,
            0x2f684bda12f684bd,
            0x684bda12f684bda1,
            0x4bda12f684bda12f,
        ]),
        Fp::from_raw([
            0xa7bf8192bfd2a76f,
            0x0a3d21162f0d6299,
            0xf3a70c3fa8fe337e,
            0x6484aa716545ca2c,
        ]),
        Fp::from_raw([
            0xdfb425d2685c2573,
            0x9467c1bfc8e8d978,
            0xd5e9e6632722c298,
            0x7a06534bb8bdb49f,
        ]),
        Fp::from_raw([
            0xfffffffefffff93b,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
        ]),
    ];

    /// Z = -11
    pub const Z: Fp = Fp::from_raw([
        0xfffffffefffffc24,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
    ]);

    /// `(F::ROOT_OF_UNITY.invert().unwrap() * z).sqrt().unwrap()`
    pub const THETA: Fp = Fp::from_raw([
        0x286729c8303c4a59,
        0xec184f00a74789dd,
        0x7ad13fb38f842afe,
        0x31fdf302724013e5,
    ]);
}

impl CurveAffineExt for Secp256k1Affine {
    batch_add!();

    fn into_coordinates(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }
}

#[test]
fn test_hash_to_curve() {
    assert_eq!(Fp::ZERO - Fp::from(11), Secp256k1::Z);
    assert_eq!(
        (Fp::ROOT_OF_UNITY.invert().unwrap() * Secp256k1::Z)
            .sqrt()
            .unwrap(),
        Secp256k1::THETA,
    );
    crate::tests::curve::hash_to_curve_test::<Secp256k1>();
}

#[test]
fn test_curve() {
    crate::tests::curve::curve_tests::<Secp256k1>();
}

#[test]
fn test_serialization() {
    crate::tests::curve::random_serialization_test::<Secp256k1>();
    #[cfg(feature = "derive_serde")]
    crate::tests::curve::random_serde_test::<Secp256k1>();
}

#[test]
fn test_endo_consistency() {
    let g = Secp256k1::generator();
    assert_eq!(g * Fq::ZETA, g.endo());
}

#[test]
fn ecdsa_example() {
    use crate::group::Curve;
    use crate::CurveAffine;
    use ff::FromUniformBytes;
    use rand_core::OsRng;

    fn mod_n(x: Fp) -> Fq {
        let mut x_repr = [0u8; 32];
        x_repr.copy_from_slice(x.to_repr().as_ref());
        let mut x_bytes = [0u8; 64];
        x_bytes[..32].copy_from_slice(&x_repr[..]);
        Fq::from_uniform_bytes(&x_bytes)
    }

    let g = Secp256k1::generator();

    for _ in 0..1000 {
        // Generate a key pair
        let sk = Fq::random(OsRng);
        let pk = (g * sk).to_affine();

        // Generate a valid signature
        // Suppose `m_hash` is the message hash
        let msg_hash = Fq::random(OsRng);

        let (r, s) = {
            // Draw arandomness
            let k = Fq::random(OsRng);
            let k_inv = k.invert().unwrap();

            // Calculate `r`
            let r_point = (g * k).to_affine().coordinates().unwrap();
            let x = r_point.x();
            let r = mod_n(*x);

            // Calculate `s`
            let s = k_inv * (msg_hash + (r * sk));

            (r, s)
        };

        {
            // Verify
            let s_inv = s.invert().unwrap();
            let u_1 = msg_hash * s_inv;
            let u_2 = r * s_inv;

            let v_1 = g * u_1;
            let v_2 = pk * u_2;

            let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
            let x_candidate = r_point.x();
            let r_candidate = mod_n(*x_candidate);

            assert_eq!(r, r_candidate);
        }
    }
}
