use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::bigint::split_into_fixed_number_of_limbs;
use franklin_crypto::plonk::circuit::bigint::{biguint_to_fe, fe_to_biguint, repr_to_biguint};
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::{u64_exp_to_ff, u64_to_ff};
use franklin_crypto::bellman::pairing::ff::PrimeField;

use super::range::*;

pub trait NumExtension<E: Engine> : Sized {
    fn weighted_sum<CS: ConstraintSystem<E>>(cs: &mut CS, inputs: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>;
    fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError>;
    fn from_be_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError>;
    fn split_into_limbs<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bit_length: usize) -> Result<Vec<Self>, SynthesisError>;
    fn split_into_fixed_number_of_limbs<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bit_length: usize, num_limbs: usize) -> Result<Vec<Self>, SynthesisError>;
    fn divmod<CS: ConstraintSystem<E>>(&self, cs: &mut CS, denom: usize) -> Result<(Self, Self), SynthesisError>;
}

impl<E: Engine> NumExtension<E> for Num<E> {
    fn weighted_sum<CS: ConstraintSystem<E>>(cs: &mut CS, inputs: &[Self], base: &E::Fr) -> Result<Self, SynthesisError> {
        let mut acc = Num::zero();
        for inp in inputs {
            // compute acc = acc * base + inp in one gate
            acc = Num::fma_with_coefficients(
                cs,
                &acc,
                &Num::Constant(*base),
                &inp,
                E::Fr::one(),
                E::Fr::one()
            )?;
        }
        Ok(acc)
    }

    fn from_be_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let nums: Vec<Num<E>> = bytes.iter().map(|b| b.into_num()).collect();
        assert!(nums.len() * 8 <= E::Fr::CAPACITY as usize);
        Num::weighted_sum(cs, nums.as_slice(), &E::Fr::from_str("256").unwrap())
    }

    fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let reversed = bytes.into_iter().cloned().rev().collect::<Vec<Byte<E>>>();
        Self::from_be_bytes(cs, reversed.as_slice())
    }

    fn split_into_limbs<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bit_length: usize) -> Result<Vec<Self>, SynthesisError> {
        let bits = E::Fr::CAPACITY as usize;
        let num_limbs = (bits + bit_length - 1) / bit_length;
        self.split_into_fixed_number_of_limbs(cs, bit_length, num_limbs)
    }

    fn split_into_fixed_number_of_limbs<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bit_length: usize, num_limbs: usize) -> Result<Vec<Self>, SynthesisError> {
        assert!(num_limbs * bit_length <= E::Fr::CAPACITY as usize);

        let values = self
            .get_value()
            .map(|v| split_into_fixed_number_of_limbs(fe_to_biguint(&v), bit_length, num_limbs));

        let limbs = (0..num_limbs)
            .map(|i| Num::alloc(cs, values.as_ref().map(|vs| biguint_to_fe(vs[i].clone()))))
            .collect::<Result<Vec<_>, _>>()?;

        // constrain all but the last limb based on the bit_length
        for l in &limbs[..num_limbs - 1] {
            constrain_bit_length(cs, l, bit_length)?;
        }

        if num_limbs * bit_length == E::Fr::CAPACITY as usize {
            // constrain the last limb based on the field modulus
            let modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
            let bound = modulus >> (bit_length * (num_limbs - 1));
            check_less_or_equal(cs, limbs.last().unwrap(), biguint_to_fe(bound))?;
        } else {
            constrain_bit_length(cs, limbs.last().unwrap(), bit_length)?;
        }


        let mut reversed = limbs.clone();
        reversed.reverse();
        let sum = Num::weighted_sum(cs, &reversed, &u64_exp_to_ff(2, bit_length as u64))?;
        sum.enforce_equal(cs, self)?;
        Ok(limbs)
    }

    fn divmod<CS: ConstraintSystem<E>>(&self, cs: &mut CS, denom: usize) -> Result<(Self, Self), SynthesisError> {
        let (quo_val, rem_val) = self.get_value().map(|n| {
            let n = fe_to_biguint(&n);
            let quo = n.clone() / denom;
            let rem = n % denom;
            (biguint_to_fe(quo), biguint_to_fe(rem))
         }).unzip();

        let quo = Num::alloc(cs, quo_val)?;
        let rem = Num::alloc(cs, rem_val)?;

        // constrain rem + 1 <= denom
        let remp1 = rem.add(cs, &Num::one())?;
        check_less_or_equal_usize(cs, &remp1, denom)?;

        let max_quo = repr_to_biguint::<E::Fr>(&E::Fr::char()) / denom;
        check_less_or_equal(cs, &quo, biguint_to_fe(max_quo))?;

        let denom = Num::Constant(u64_to_ff(denom as u64));
        let reconstructed = Num::fma_with_coefficients(cs, &quo, &denom, &rem, E::Fr::one(), E::Fr::one())?;
        reconstructed.enforce_equal(cs, self)?;

        Ok((quo, rem))
    }
}

#[derive(Clone,Copy,Debug)]
pub struct Nibble<E: Engine> {
    byte: Byte<E>,
}

impl<E: Engine> Nibble<E> {
    fn alloc_impl<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>, constrain: bool) -> Result<Self, SynthesisError> {
        if let Some(value) = value {
            assert!(value < 16);
        }

        let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
        if constrain {
            constrain_bit_length(cs, &num, 4)?;
        }
        let byte = Byte::from_num_unconstrained(cs, num);
        Ok(Self { byte })
    }

    pub fn alloc_unconstrained<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, value, false)
    }

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, value, true)
    }

    pub fn constant(value: u8) -> Self {
        assert!(value < 16);
        Self { byte: Byte::constant(value) }
    }

    pub fn zero() -> Self {
        Self { byte: Byte::zero() }
    }

    pub fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.byte.into_num(), &b.byte.into_num())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        Ok( Self { byte: Byte::conditionally_select(cs, flag, &a.byte, &b.byte)? } )
    }

    pub fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError> {
        constrain_bit_length(cs, &num, 4)?;
        let byte = Byte::from_num_unconstrained(cs, num);
        Ok(Self { byte })
    }

    pub fn to_byte(&self) -> Byte<E> { self.byte }
}

pub trait ToNibbles<E: Engine, const N: usize> {
    fn to_be_nibbles<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Nibble<E>; N], SynthesisError>;
}

impl<E: Engine> ToNibbles<E, 2> for Byte<E> {
    fn to_be_nibbles<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Nibble<E>; 2], SynthesisError> {
        let value = self.get_byte_value();

        let res = [
            Nibble::alloc(cs, value.map(|v| v >> 4))?,
            Nibble::alloc(cs, value.map(|v| v & 0xf))?,
        ];

        let base = E::Fr::from_str("16").unwrap();
        let elts = &[res[0].to_byte().into_num(), res[1].to_byte().into_num()];
        let num = Num::weighted_sum(cs, elts, &base)?;
        self.into_num().enforce_equal(cs, &num)?;
        Ok(res)
    }
}