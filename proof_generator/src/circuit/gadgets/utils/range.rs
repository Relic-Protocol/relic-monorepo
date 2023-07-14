use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::{Field, PrimeField, Engine, SynthesisError};
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::bigint::{fe_to_biguint, constraint_num_bits};
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

pub const fn bit_length(n: usize) -> usize {
    (usize::BITS - n.leading_zeros()) as usize
}

pub const fn byte_length(n: usize) -> usize {
    (bit_length(n) + 7) / 8
}

pub fn constrain_bit_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    bits: usize
) -> Result<(), SynthesisError> {
    match num {
        Num::Constant(v) => {
            let v = fe_to_biguint(v);
            let max = fe_to_biguint(&E::Fr::one()) << bits;
            assert!(v < max, "range check will fail");
        },
        Num::Variable(var) => {
            if let Some(v) = var.get_value() {
                let v = fe_to_biguint(&v);
                let max = fe_to_biguint(&E::Fr::one()) << bits;
                assert!(v < max, "range check will fail");
            }
            constraint_num_bits(cs, num, bits)?;
        }
    }
    Ok(())
}

// bits is a known bound on the bit length of a
pub fn check_greater_or_equal<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &Num<E>,
    bits: usize,
    bound: E::Fr
) -> Result<(), SynthesisError> {
    if bound == E::Fr::zero() {
        return Ok(())
    }

    // we can only range check for multiples of 8 bits
    let rounded_bits = 8 * ((bits + 7) / 8);

    // our check only works if the bound on a is smaller than the capacity
    assert!(rounded_bits < E::Fr::CAPACITY as usize);

    let bound_num = Num::Constant(bound);
    let diff = a.sub(cs, &bound_num)?;

    constrain_bit_length(cs, &diff, rounded_bits)
}

// bits is a known bound on the bit length of a
pub fn check_greater_or_equal_usize<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &Num<E>,
    bits: usize,
    bound: usize
) -> Result<(), SynthesisError> {
    check_greater_or_equal(cs, a, bits, u64_to_ff(bound as u64))
}

pub fn check_less_or_equal<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &Num<E>,
    bound: E::Fr
) -> Result<(), SynthesisError> {
    let bound_bigint = fe_to_biguint(&bound);
    // we can only range check for multiples of 8 bits
    let bound_bits = 8 * ((7 + bound_bigint.bits() as usize) / 8);
    assert!(bound_bits < E::Fr::CAPACITY as usize);
    if bound_bits == 0 {
        return a.enforce_equal(cs, &Num::zero())
    }

    let bound_num = Num::Constant(bound);
    let diff = bound_num.sub(cs, a)?;
    
    // prevent extreme underflow
    constrain_bit_length(cs, &a, bound_bits)?;

    // detect if a small underflow occurred
    constrain_bit_length(cs, &diff, bound_bits)
}

pub fn check_less_or_equal_usize<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &Num<E>,
    bound: usize
) -> Result<(), SynthesisError> {
    check_less_or_equal(cs, a, u64_to_ff(bound as u64))
}
