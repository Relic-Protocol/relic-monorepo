use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use bellman::pairing::{Engine};
use std::marker::PhantomData;
use super::group_hash::GroupHasher;

use rand::{Rand, Rng};

pub mod bn256;
pub mod jive_transcript;

pub trait JiveParams: Clone {
    fn use_custom_gate(&self) -> bool;
    fn set_allow_custom_gate(&mut self, allow: bool);
}

pub trait JiveEngine : Engine {
    type Params: JiveParams;

    const ROUNDS: usize;
    const ROUND_CONSTANTS_C: &'static [&'static str];
    const ROUND_CONSTANTS_D: &'static [&'static str];
    const DELTA: &'static str;
    const ALPHA_INV: &'static str;
}

/*
function sbox(uint256 x, uint256 y) internal view returns (uint256, uint256) {
    x = addmod(x, q - mulmod(beta, mulmod(y, y, q), q), q);
    y = addmod(y, q - expmod(x, alpha_inv, q), q);
    x = addmod(addmod(x, mulmod(beta, mulmod(y, y, q), q), q), delta, q);
    return (x, y);
}

function ll(uint256 x, uint256 y) internal pure returns (uint256 r0, uint256 r1) {
    r0 = addmod(x, mulmod(5, y, q), q);
    r1 = addmod(y, mulmod(5, r0, q), q);
}

function compress(uint256 x, uint256 y) internal view returns (uint256) {
    uint256 sum = addmod(x, y, q);
    uint256 c;
    uint256 d;
    for (uint256 r = 0; r < 19; r++) {
        (c, d) = CD(r);
        x = addmod(x, c, q);
        y = addmod(y, d, q);
        (x, y) = ll(x, y);
        (x, y) = sbox(x, y);
    }
    (x, y) = ll(x, y);
    return addmod(addmod(x, y, q), sum, q);
}
*/

fn sbox<E: JiveEngine>(mut x: E::Fr, mut y: E::Fr) -> (E::Fr, E::Fr) {
    let beta = E::Fr::from_str("5").unwrap();
    let mut byy = beta.clone();
    byy.mul_assign(&y);
    byy.mul_assign(&y);
    x.sub_assign(&byy);
    y.sub_assign(&x.pow(&E::Fr::from_str(E::ALPHA_INV).unwrap().into_repr()));
    byy = beta;
    byy.mul_assign(&y);
    byy.mul_assign(&y);
    byy.add_assign(&E::Fr::from_str(E::DELTA).unwrap());
    x.add_assign(&byy);
    (x, y)
}

fn ll<E: JiveEngine>(x: E::Fr, y: E::Fr) -> (E::Fr, E::Fr) {
    let beta = E::Fr::from_str("5").unwrap();
    let mut r0 = beta.clone();
    r0.mul_assign(&y);
    r0.add_assign(&x);
    let mut r1 = r0.clone();
    r1.mul_assign(&beta);
    r1.add_assign(&y);
    (r0, r1)
}

pub fn jive_2_1<E: JiveEngine>(mut x: E::Fr, mut y: E::Fr, _params: &E::Params) -> E::Fr {
    let C: Vec<_> = E::ROUND_CONSTANTS_C.iter().map(|s| E::Fr::from_str(s).unwrap()).collect();
    let D: Vec<_> = E::ROUND_CONSTANTS_D.iter().map(|s| E::Fr::from_str(s).unwrap()).collect();
    let mut sum = x.clone();
    sum.add_assign(&y);
    for r in 0..19 {
        let (c, d) = (C[r], D[r]);
        x.add_assign(&c);
        y.add_assign(&d);
        (x, y) = ll::<E>(x, y);
        (x, y) = sbox::<E>(x, y);
    }
    (x, y) = ll::<E>(x, y);
    let mut result = x.clone();
    result.add_assign(&y);
    result.add_assign(&sum);
    result
}

#[derive(Clone, Debug)]
pub struct StatefulJive<'a, E: JiveEngine> {
    pub params: &'a E::Params,
    state: Option<E::Fr>
}

impl<'a, E: JiveEngine> StatefulJive<'a, E> {
    pub fn new(
        params: &'a E::Params
    ) -> Self {
        StatefulJive::<_> {
            params,
            state: None
        }
    }

    pub fn absorb_single_value(
        &mut self,
        value: E::Fr
    ) {
        if let Some(s) = self.state {
            self.state = Some(jive_2_1::<E>(s, value, self.params));
        } else {
            self.state = Some(value);
        }
    }

    pub fn absorb(
        &mut self,
        input: &[E::Fr]
    ) {
        for i in input {
            self.absorb_single_value(*i);
        }
    }

    pub fn squeeze_out_single(
        &mut self,
    ) -> E::Fr {
        if let Some(mut s) = self.state {
            s = jive_2_1::<E>(s, s, self.params);
            self.state = Some(s);
            s
        } else {
            panic!("cannot squeeze without first absorbing")
        }
    }
}