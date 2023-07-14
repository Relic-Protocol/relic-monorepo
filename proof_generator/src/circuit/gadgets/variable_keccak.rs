use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::byte::Byte;

use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::{
    DEFAULT_KECCAK_DIGEST_WORDS_SIZE, KECCAK_RATE_WORDS_SIZE, KECCAK_LANE_WIDTH,
    Keccak256Gadget, KeccakState, KeccakStateBase
};

use tiny_keccak::{Keccak, Hasher};

use super::utils::digest::{Digest, RawDigest};
use super::utils::num::NumExtension;
use super::utils::pad::multi_rate_pad;
use super::utils::vec::VarVec;

pub const KECCAK_DIGEST_NUM_WORDS: usize = DEFAULT_KECCAK_DIGEST_WORDS_SIZE;
pub const KECCAK_DIGEST_NUM_BYTES: usize = DEFAULT_KECCAK_DIGEST_WORDS_SIZE * 8;

#[derive(Debug)]
pub struct KeccakGadget<E: Engine> {
    gadget: Keccak256Gadget<E>
}

pub type RawKeccakDigest<E> = RawDigest<E, KECCAK_DIGEST_NUM_WORDS, 8>;
pub type KeccakDigest<E> = Digest<E, KECCAK_DIGEST_NUM_WORDS, 8>;

impl<E: Engine> KeccakGadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;
        Ok(Self { gadget })
    }

    fn pad_and_convert<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>>
    ) -> Result<(Num<E>, Vec<Num<E>>), SynthesisError> {
        let block_size = KECCAK_RATE_WORDS_SIZE * (KECCAK_LANE_WIDTH / 8);
        let (block_cnt, padded) = multi_rate_pad(cs, input, block_size)?;
        // now convert the byte array to array of 64-bit words
        let words64 = padded.chunks(8).map(|bytes| Num::from_le_bytes(cs, bytes)).collect::<Result<Vec<_>,_>>()?;
        Ok((block_cnt, words64))
    }

    pub fn digest<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>>
    ) -> Result<KeccakDigest<E>, SynthesisError> {
        let min = input.length().lower();
        let max = input.length().upper();

        let min_input_blocks = (min + 8 * KECCAK_RATE_WORDS_SIZE) / (8 * KECCAK_RATE_WORDS_SIZE);
        let max_input_blocks = (max + 8 * KECCAK_RATE_WORDS_SIZE) / (8 * KECCAK_RATE_WORDS_SIZE);

        let (block_cnt, words64) = self.pad_and_convert(cs, input)?;
        let mut output = [Num::<E>::zero(); DEFAULT_KECCAK_DIGEST_WORDS_SIZE];

        let mut keccak_state = KeccakState::default();
        let mut block_idx = Num::zero();
        let mut words_iter = words64.iter();
        for block in 0..max_input_blocks+1 {
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

                if block >= min_input_blocks {
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
        RawKeccakDigest::from_bytes(result)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::utils::vec::{VarVecMN, Vecable};
    use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use franklin_crypto::bellman::pairing::bn256::Bn256;
    use franklin_crypto::rescue::bn256::Bn256RescueParams;
    use franklin_crypto::plonk::circuit::byte::Byte;

    #[test]
    fn test_keccak() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;

        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        let mut params = Bn256RescueParams::new_checked_2_into_1();
        params.set_allow_custom_gate(true);
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        const M: usize = 500;
        const N: usize = 600;
        let gadget: KeccakGadget<E> = KeccakGadget::new(cs).unwrap();
        for _ in 0..20 {
            let len = rng.gen_range(M, N);
            let raw = std::iter::from_fn(|| Some(rng.gen::<u8>())).take(len).collect::<Vec<_>>();
            let input = VarVecMN::<E, Byte<E>, M, N>::alloc(cs, Some(raw.clone())).unwrap();

            let raw_digest = KeccakGadget::<E>::raw_digest(raw.as_slice());
            let digest = gadget.digest(cs, &input).unwrap();
            digest.enforce_equal(cs, &KeccakDigest::constant(raw_digest)).unwrap();
        }

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}