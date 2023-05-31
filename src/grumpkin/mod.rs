mod curve;

pub use crate::bn256::{Fq as Fr, Fr as Fq};
pub use curve::*;

pub type Base = Fq;
pub type Scalar = Fr;
pub type Point = G1;
pub type Affine = G1Affine;
pub type Compressed = G1Compressed;
