use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::*;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::bigint::{split_into_slices, split_some_into_slices};
use super::allocated_num::*;
use super::linear_combination::*;
use super::boolean::Boolean;
use super::utils::*;
use crate::plonk::circuit::Assignment;
use crate::plonk::circuit::bigint_new::constraint_bit_length;

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm
};

#[derive(Clone, Debug)]
pub struct Byte<E: Engine> {
    pub inner: Num<E>
}

impl<E: Engine> Copy for Byte<E> {}

impl<E: Engine> Byte<E> {
    pub fn empty() -> Self {
        Self {
            inner: Num::Constant(E::Fr::zero())
        }
    }

    pub fn zero() -> Self {
        Self {inner: Num::Constant(E::Fr::zero())}
    }

    pub fn into_num(&self) -> Num<E> {
        self.inner.clone()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.inner.get_value()
    }

    pub fn get_byte_value(&self) -> Option<u8> {
        if let Some(v) = self.get_value() {
            let repr = v.into_repr();
            let bits = repr.num_bits();
            assert!(bits <= 8);
            let byte = repr.as_ref()[0] as u8;

            Some(byte)
        } else {
            None
        }
    }
    
    pub fn from_u8_witness<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        let var = AllocatedNum::alloc(
            cs,
            || {
                let as_u8 = *value.get()?;
                let fe = u64_to_fe(as_u8 as u64);

                Ok(fe)
            }
        )?;
        let num = Num::Variable(var);
        constraint_bit_length(cs, &var, 8)?;

        Ok(
            Self {
                inner: num
            }
        )
    }

    pub fn from_u8_witness_multiple<CS: ConstraintSystem<E>, const N: usize>(cs: &mut CS, value: Option<[u8; N]>) -> Result<[Self; N], SynthesisError> {
        let mut result = [Self::zero(); N];

        for i in 0..N {
            let wit = value.as_ref().map(|el| el[i]);
            result[i] = Self::from_u8_witness(cs, wit)?;
        }

        Ok(result)
    }

    pub fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, value: Num<E>) -> Result<Self, SynthesisError> {
        if value.is_constant() {
            let var = value.get_variable();
            constraint_bit_length(cs, &var, 8)?;
        }
       
        Ok(
            Self {
                inner: value
            }
        )
    }

    pub fn from_num_unconstrained<CS: ConstraintSystem<E>>(_cs: &mut CS, value: Num<E>) -> Self {
        Self {
            inner: value
        }
    }

    pub fn constant(value: u8) -> Self {
        let value = E::Fr::from_str(&value.to_string()).expect("must convert constant u8");
        Self {
            inner : Num::Constant(value)
        }
    }

    pub fn from_cnst(value: E::Fr) -> Self {
        let bits = value.into_repr().num_bits();
        if bits > 8 {
            panic!("Invalid bit length of Byte constant");
        }
        Self {
            inner : Num::Constant(value)
        }
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        let new_inner = Num::conditionally_select(cs, flag, &a.inner, &b.inner)?;
        let new = Self {
            inner : new_inner
        };

        Ok(new)
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Boolean, SynthesisError> {
        self.inner.is_zero(cs)
    }

    pub fn get_value_multiple<const N: usize>(els: &[Self; N]) -> Option<[E::Fr; N]> {
        let mut tmp = [E::Fr::zero(); N];
        for (el, v) in els.iter().zip(tmp.iter_mut()) {
            if let Some(val) = el.get_value() {
                *v = val;
            } else {
                return None;
            }
        }

        Some(tmp)
    }

    pub fn get_byte_value_multiple<const N: usize>(els: &[Self; N]) -> Option<[u8; N]> {
        let mut tmp = [0u8; N];
        for (el, v) in els.iter().zip(tmp.iter_mut()) {
            if let Some(val) = el.get_byte_value() {
                *v = val;
            } else {
                return None;
            }
        }

        Some(tmp)
    }
}

// NOTE: there are default infinitely recursive implementations here, so implementor should override at least one of them!
pub trait IntoBytes<E: Engine> {
    fn encoding_len() -> usize {
        unimplemented!("Usually there is an outside known constant for it. Later on we should move to const generics here");
    }
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_be_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}

pub fn uniquely_encode_le_bytes_into_num<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Num<E>, SynthesisError> {
    assert!(bytes.len() <= (E::Fr::CAPACITY / 8) as usize);
    let mut lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();
    let shift = E::Fr::from_str("256").unwrap();
    // first byte goes into the lowest bits
    for b in bytes.iter() {
        lc.add_assign_number_with_coeff(&b.into_num(), coeff);
        coeff.mul_assign(&shift);
    }

    let result = lc.into_num(cs)?;

    Ok(result)
}

pub fn uniquely_encode_be_bytes_into_num<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Num<E>, SynthesisError> {
    assert!(bytes.len() <= (E::Fr::CAPACITY / 8) as usize);
    let mut lc = LinearCombination::zero();
    let mut coeff = E::Fr::one();
    let shift = E::Fr::from_str("256").unwrap();
    // last byte goes into the lowest bits
    for b in bytes.iter().rev() {
        lc.add_assign_number_with_coeff(&b.into_num(), coeff);
        coeff.mul_assign(&shift);
    }

    let result = lc.into_num(cs)?;

    Ok(result)
}

pub fn uniquely_encode_be_bytes<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Vec<Num<E>>, SynthesisError> {
    let max_chunk = (E::Fr::CAPACITY / 8) as usize;
    let shift = E::Fr::from_str("256").unwrap();

    let mut results = vec![];
    let mut tmp = bytes.to_vec();
    tmp.reverse();
    for chunk in tmp.chunks(max_chunk) {
        let mut coeff = E::Fr::one();
        let mut lc = LinearCombination::zero();
        // last byte goes into the lowest bits
        for b in chunk.iter() {
            lc.add_assign_number_with_coeff(&b.into_num(), coeff);
            coeff.mul_assign(&shift);
        }

        let result = lc.into_num(cs)?;

        results.push(result);
    }
    
    Ok(results)
}


pub fn uniquely_encode_be_bytes_to_field_elements<F: PrimeField>(
    bytes: &[u8],
) -> Vec<F> {
    let max_chunk = (F::CAPACITY / 8) as usize;
    let shift = F::from_str("256").unwrap();

    let mut results = vec![];
    let mut tmp = bytes.to_vec();
    tmp.reverse();
    for chunk in tmp.chunks(max_chunk) {
        let mut result = F::zero();
        let mut coeff = F::one();
        for &b in chunk.iter() {
            let mut b = u64_to_fe::<F>(b as u64);
            b.mul_assign(&coeff);
            result.add_assign(&b);

            coeff.mul_assign(&shift);
        }

        results.push(result);
    }
    
    results
}

pub fn num_into_bytes_le<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    limb: Num<E>,
    width: usize
) -> Result<Vec<Byte<E>>, SynthesisError> {
    assert!(width % 8 == 0);

    let num_bytes = width / 8;
    let result = match &limb {
        Num::Variable(ref var) => {
            let mut minus_one = E::Fr::one();
            minus_one.negate();
            let factor = E::Fr::from_str("256").unwrap();
            let mut coeff = E::Fr::one();
            let mut result = Vec::with_capacity(num_bytes);
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&limb, minus_one);
            let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
            for w in witness.into_iter() {
                let allocated = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(*w.get()?)
                    }
                )?;
                let num = Num::Variable(allocated);
                let byte = Byte::from_num(cs, num.clone())?;
                result.push(byte);

                lc.add_assign_number_with_coeff(&num, coeff);
                coeff.mul_assign(&factor);
            }

            lc.enforce_zero(cs)?;

            result
        },
        Num::Constant(constant) => {
            let mut result = Vec::with_capacity(num_bytes);
            let witness = split_into_slices(constant, 8, num_bytes);
            for w in witness.into_iter() {
                let num = Num::Constant(w);
                let byte = Byte::from_num(cs, num)?;
                result.push(byte);
            }

            result
        }
    };
    
    Ok(result)
}

pub fn num_into_bytes_be<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    limb: Num<E>,
    width: usize
) -> Result<Vec<Byte<E>>, SynthesisError> {
    let mut encoding = num_into_bytes_le(cs, limb, width)?;
    encoding.reverse();

    Ok(encoding)
}

impl<E: Engine> IntoBytes<E> for Num<E> {
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut num_bytes = (E::Fr::NUM_BITS / 8) as usize;
        if E::Fr::NUM_BITS % 8 != 0 {
            num_bytes += 1;
        }

        let result = match self {
            Num::Variable(ref var) => {
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                let factor = E::Fr::from_str("256").unwrap();
                let mut coeff = E::Fr::one();
                let mut result = Vec::with_capacity(num_bytes);
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self, minus_one);
                let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
                for w in witness.into_iter() {
                    let allocated = AllocatedNum::alloc(
                        cs,
                        || {
                            Ok(*w.get()?)
                        }
                    )?;
                    let num = Num::Variable(allocated);
                    let byte = Byte::from_num(cs, num.clone())?;
                    result.push(byte);

                    lc.add_assign_number_with_coeff(&num, coeff);
                    coeff.mul_assign(&factor);
                }

                lc.enforce_zero(cs)?;

                result
            },
            Num::Constant(constant) => {
                let mut result = Vec::with_capacity(num_bytes);
                let witness = split_into_slices(constant, 8, num_bytes);
                for w in witness.into_iter() {
                    let num = Num::Constant(w);
                    let byte = Byte::from_num(cs, num)?;
                    result.push(byte);
                }

                result
            }
        };
        
        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}


impl<E: Engine> IntoBytes<E> for Boolean {
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let num_bytes = 1;

        let result = match self {
            Boolean::Is(bit) => {
                let fe_value = bit.get_value().map(|el| {
                    if el {
                        E::Fr::one()
                    } else {
                        E::Fr::zero()
                    }
                });
                let as_num = Num::Variable(
                    AllocatedNum {
                        variable: bit.get_variable(),
                        value: fe_value
                    }
                );
                
                let byte = Byte {
                    inner: as_num
                };

                vec![byte]
            },
            s @ Boolean::Not(..) => {
                let fe_value = s.get_value().map(|el| {
                    if el {
                        E::Fr::one()
                    } else {
                        E::Fr::zero()
                    }
                });
                let as_num = Num::Variable(
                    AllocatedNum::alloc(cs, || Ok(*fe_value.get()?))?
                );

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&as_num, minus_one);
                lc.add_assign_boolean_with_coeff(&s, E::Fr::one());
                lc.enforce_zero(cs)?;
                
                let byte = Byte {
                    inner: as_num
                };

                vec![byte]
            }
            Boolean::Constant(bit) => {
                vec![Byte::<E>::constant(*bit as u8)]
            }
        };

        assert_eq!(result.len(), num_bytes);
        
        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        self.into_le_bytes(cs)
    }
}