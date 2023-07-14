use franklin_crypto::bellman::{SynthesisError, Engine};
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::Field;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::boolean::Boolean;

use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

use super::vec::VarVec;

pub fn multi_rate_pad<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    input: &VarVec<E, Byte<E>>,
    block_size: usize
) -> Result<(Num<E>, Vec<Byte<E>>), SynthesisError> {
    let min = input.length().lower();
    let max = input.length().upper();

    let mut padded = vec![];

    // take first M (min input size) bytes as-is
    padded.extend(&input.vals()[..min]);

    let last_block_size = max % block_size;
    let padded_len = max + (block_size - last_block_size);

    // fill the rest with zeros for now
    padded.extend(std::iter::repeat(Byte::from_cnst(E::Fr::zero())).take(padded_len - padded.len()));

    // default value is maximum to avoid proving edge cases
    let mut block_cnt = Num::Constant(u64_to_ff((padded_len / block_size) as u64));
    let mut reached_end = Boolean::Constant(false);

    for i in min..=max {
        let idx = Num::Constant(u64_to_ff(i as u64));
        let is_end = Num::equals(cs, &idx, &input.length().to_num())?;
        let num_blocks = Num::Constant(u64_to_ff((i / block_size + 1) as u64));
        let padlen = block_size - i % block_size;

        block_cnt = Num::conditionally_select(cs, &is_end, &num_blocks, &block_cnt)?;
        reached_end = Boolean::or(cs, &reached_end, &is_end)?;
        if i < max {
            padded[i] = Byte::conditionally_select(cs, &reached_end, &padded[i], &input.vals()[i])?;
        }

        if padlen == 1 {
            padded[i] = Byte::conditionally_select(
                cs,
                &is_end,
                &Byte::from_cnst(u64_to_ff(0x81)),
                &padded[i]
            )?;
        } else {
            padded[i] = Byte::conditionally_select(
                cs,
                &is_end,
                &Byte::from_cnst(u64_to_ff(0x01)),
                &padded[i]
            )?;
            padded[i + padlen - 1] = Byte::conditionally_select(
                cs,
                &is_end,
                &Byte::from_cnst(u64_to_ff(0x80)),
                &padded[i + padlen - 1]
            )?;
        }
    }

    Ok((block_cnt, padded))
}

pub fn multi_rate_pad_raw(
    input: &[u8],
    block_size: usize
) -> Vec<u8> {
    let last_block_size = input.len() % block_size;
    let padlen = block_size - last_block_size;
    let padded_len = input.len() + padlen;

    let mut result = Vec::with_capacity(padded_len);
    result.extend(input.iter());
    if padlen == 1 {
        result.push(0x81);
    } else {
        result.push(0x01);
        result.extend(std::iter::repeat(0x00).take(padlen - 2));
        result.push(0x80);
    }
    result
}