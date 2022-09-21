use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::boolean::Boolean;

use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;
use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::{
    DEFAULT_KECCAK_DIGEST_WORDS_SIZE, KECCAK_RATE_WORDS_SIZE, KECCAK_LANE_WIDTH,
    Keccak256Gadget, KeccakState, KeccakStateBase
};

use tiny_keccak::{Keccak, Hasher};

use super::{Digest, RawDigest, NumExtension, VarVec};

pub const KECCAK_DIGEST_NUM_WORDS: usize = DEFAULT_KECCAK_DIGEST_WORDS_SIZE;
pub const KECCAK_DIGEST_NUM_BYTES: usize = DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8;

#[derive(Debug)]
pub struct KeccakGadget<E: Engine, const N: usize, const M: usize> {
    min_input_blocks: usize,
    max_input_blocks: usize,
    gadget: Keccak256Gadget<E>
}

pub type RawKeccakDigest<E> = RawDigest<E, KECCAK_DIGEST_NUM_WORDS>;
pub type KeccakDigest<E> = Digest<E, KECCAK_DIGEST_NUM_WORDS>;

// N = min input size
// M = max input size
impl<E: Engine, const N: usize, const M: usize> KeccakGadget<E, N, M> {

    // type Input = VarVec<E, Byte<E>, M>;
    // no inherent associated types yet :(

    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        assert!(N <= M);
        let min_input_blocks = (N + 8 * KECCAK_RATE_WORDS_SIZE) / (8 * KECCAK_RATE_WORDS_SIZE);
        let max_input_blocks = (M + 8 * KECCAK_RATE_WORDS_SIZE) / (8 * KECCAK_RATE_WORDS_SIZE);
        let gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;
        Ok(Self { gadget, min_input_blocks, max_input_blocks })
    }

    fn pad<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>, M>
    ) -> Result<(Num<E>, Vec<Byte<E>>), SynthesisError> {
        let mut padded = vec![];

        // take first N (min input size) bytes as-is
        padded.extend(&input.vals[..N]);

        let block_size = KECCAK_RATE_WORDS_SIZE * (KECCAK_LANE_WIDTH / 8);
        let last_block_size = M % block_size;
        let padded_len = M + (block_size - last_block_size);

        // fill the rest with zeros for now
        padded.extend(std::iter::repeat(Byte::from_cnst(E::Fr::zero())).take(padded_len - padded.len()));

        let mut idx = Num::Constant(u64_to_ff(N as u64));

        // default value is maximum to avoid proving edge cases
        let mut block_cnt = Num::Constant(u64_to_ff((padded_len / block_size) as u64));
        let mut reached_end = Boolean::Constant(false);

        for i in N..=M {
            let is_end = Num::equals(cs, &idx, &input.length())?;
            let num_blocks = Num::Constant(u64_to_ff((i / block_size + 1) as u64));
            let padlen = block_size - i % block_size;

            block_cnt = Num::conditionally_select(cs, &is_end, &num_blocks, &block_cnt)?;
            reached_end = Boolean::or(cs, &reached_end, &is_end)?;
            if i < M {
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
            idx = idx.add(cs, &Num::Constant(E::Fr::one()))?;
        }

        Ok((block_cnt, padded))
    }

    fn pad_and_convert<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>, M>
    ) -> Result<(Num<E>, Vec<Num<E>>), SynthesisError> {
        let (block_cnt, padded) = self.pad(cs, input)?;
        // now convert the byte array to array of 64-bit words
        let words64 = padded.chunks(8).map(|bytes| Num::from_le_bytes(cs, bytes)).collect::<Result<Vec<_>,_>>()?;
        Ok((block_cnt, words64))
    }

    pub fn digest<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>, M>
    ) -> Result<KeccakDigest<E>, SynthesisError> {
        let (block_cnt, words64) = self.pad_and_convert(cs, input)?;
        let mut output = [Num::<E>::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        let mut keccak_state = KeccakState::default();
        let mut block_idx = Num::zero();
        let mut words_iter = words64.iter();
        for block in 0..self.max_input_blocks+1 {
            let mut elems_to_absorb = [Num::<E>::zero(); KECCAK_RATE_WORDS_SIZE];
            for (i, v) in words_iter.by_ref().take(KECCAK_RATE_WORDS_SIZE).enumerate() {
                elems_to_absorb[i] = *v;
            }
            if block == 0 {
                keccak_state = self.gadget.keccak_round_function_init(cs, &elems_to_absorb[..])?;
            } else {
                let last = Num::equals(cs, &block_idx, &block_cnt)?;

                let (new_state, supposed_output_vars) = self.gadget.keccak_round_function(
                    cs, keccak_state, elems_to_absorb, last
                )?;
                keccak_state = new_state;

                if block >= self.min_input_blocks {
                    for (a, b) in output.iter_mut().zip(supposed_output_vars.iter()) {
                        *a = Num::conditionally_select(cs, &last, b, a)?;
                    }
                }
            }

            keccak_state.base = KeccakStateBase::First;
            block_idx = block_idx.add(cs, &Num::Constant(E::Fr::one()))?;
        }

        Ok(KeccakDigest { words: output })
    }

    pub fn raw_digest(input: &[u8]) -> RawKeccakDigest<E> {
        let mut hasher = Keccak::v256();
        hasher.update(input);
        let mut result = [0u8; KECCAK_DIGEST_NUM_BYTES];
        hasher.finalize(result.as_mut_slice());
        RawKeccakDigest::from_bytes32(result)
    }
}
