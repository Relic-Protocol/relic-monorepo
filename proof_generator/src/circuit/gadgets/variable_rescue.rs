use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::byte::Byte;

use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;
use franklin_crypto::plonk::circuit::channel::ChannelGadget;
use franklin_crypto::plonk::circuit::channel::RescueChannelGadget;
use franklin_crypto::plonk::circuit::rescue::{StatefulRescueGadget};
use franklin_crypto::rescue::{RescueEngine, StatefulRescue};

use super::merkle::{MerkleGadget, MerkleCompressor};
use super::utils::digest::{Digest, RawDigest};
use super::utils::num::NumExtension;
use super::utils::pad::multi_rate_pad;
use super::utils::pad::multi_rate_pad_raw;
use super::utils::vec::VarVec;

#[derive(Clone, Debug)]
pub struct RescueGadget<'a, E: RescueEngine> {
    params: &'a E::Params
}

pub type RawRescueDigest<E> = RawDigest<E, 1, 32>;
pub type RescueDigest<E> = Digest<E, 1, 32>;

impl<'a, E: RescueEngine> RescueGadget<'a, E> {
    const BLOCK_SIZE: usize = E::Fr::CAPACITY as usize / 8;

    pub fn new(params: &'a E::Params) -> Self {
        Self { params }
    }

    fn pad_and_convert<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>>
    ) -> Result<(Num<E>, Vec<Num<E>>), SynthesisError> {
        let (block_cnt, padded) = multi_rate_pad(cs, input, Self::BLOCK_SIZE)?;
        // now convert the byte array to an array of words
        let words = padded.chunks(Self::BLOCK_SIZE).map(|bytes| Num::from_le_bytes(cs, bytes)).collect::<Result<Vec<_>,_>>()?;
        Ok((block_cnt, words))
    }

    pub fn digest<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &VarVec<E, Byte<E>>
    ) -> Result<RescueDigest<E>, SynthesisError> {
        let min = input.length().lower();
        let min_input_blocks = (min + Self::BLOCK_SIZE) / Self::BLOCK_SIZE;

        let mut rescue = RescueChannelGadget::<E>::new(&self.params);

        let (block_cnt, input_words) = self.pad_and_convert(cs, input)?;
        let mut output = Num::zero();

        for (i, word) in input_words.iter().enumerate() {
            let var = if word.is_constant() {
                AllocatedNum::alloc_cnst(cs, word.get_value().unwrap())?
            } else {
                word.get_variable()
            };
            rescue.consume(var, cs)?;
            if i >= min_input_blocks - 1 {
                let possible = Num::Variable(rescue.clone().produce_challenge(cs)?);
                let correct = Num::equals(cs, &block_cnt, &Num::Constant(u64_to_ff(i as u64 + 1)))?;
                output = Num::conditionally_select(cs, &correct, &possible, &output)?;
            }
        }

        let words = [output];
        Ok(RescueDigest { words })
    }

    pub fn compress_2_1<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: RescueDigest<E>, y: RescueDigest<E>) -> Result<RescueDigest<E>, SynthesisError> {
        let mut gadget = StatefulRescueGadget::new(self.params);
        gadget.absorb_nums(cs, &[x.words[0], y.words[0]], self.params)?;
        let lc = gadget.squeeze_out_single(cs, self.params)?;
        let words = [Num::Variable(lc.into_allocated_num(cs)?)];
        Ok(RescueDigest { words })
    }

    pub fn raw_digest(input: &[u8], params: &E::Params) -> RawRescueDigest<E> {
        let padded = multi_rate_pad_raw(input, Self::BLOCK_SIZE);
        let shift = u64_to_ff::<E::Fr>(256);
        let words =
            padded
            .chunks(Self::BLOCK_SIZE)
            .map(|bytes| bytes.iter().rev().fold(E::Fr::zero(), |mut acc, e| {
                acc.mul_assign(&shift);
                acc.add_assign(&u64_to_ff(*e as u64));
                acc
            }))
            .collect::<Vec<_>>();
        let mut rescue = StatefulRescue::<E>::new(params);
        rescue.absorb(&words);
        let result = rescue.squeeze_out_single();
        RawRescueDigest::from_words(&[result])
    }
}

impl<'a, E: RescueEngine> MerkleCompressor<E, 1, 32> for RescueGadget<'a, E> {
    type Params = &'a E::Params;

    fn compress<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: RescueDigest<E>, y: RescueDigest<E>) -> Result<RescueDigest<E>, SynthesisError> {
        self.compress_2_1(cs, x, y)
    }

    fn compress_raw(x: RawRescueDigest<E>, y: RawRescueDigest<E>, params: Self::Params) -> RawRescueDigest<E> {
        let mut rescue = StatefulRescue::<E>::new(&params);
        rescue.absorb(&[x.words[0], y.words[0]]);
        let words = [rescue.squeeze_out_single()];
        RawRescueDigest{ words }
    }
}

pub type RescueMerkleGadget<'a, E> = MerkleGadget<'a, E, 1, 32, RescueGadget<'a, E>>;

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
    fn test_rescue() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;

        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        let mut params = Bn256RescueParams::new_checked_2_into_1();
        params.set_allow_custom_gate(true);
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        const M: usize = 500;
        const N: usize = 600;
        let gadget: RescueGadget<E> = RescueGadget::new(&params);
        for _ in 0..200 {
            let len = rng.gen_range(M, N);
            let raw = std::iter::from_fn(|| Some(rng.gen::<u8>())).take(len).collect::<Vec<_>>();
            let input = VarVecMN::<E, Byte<E>, M, N>::alloc(cs, Some(raw.clone())).unwrap();

            let raw_digest = RescueGadget::<E>::raw_digest(raw.as_slice(), &params);
            let digest = gadget.digest(cs, &input).unwrap();
            digest.enforce_equal(cs, &RescueDigest::constant(raw_digest)).unwrap();
        }

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}