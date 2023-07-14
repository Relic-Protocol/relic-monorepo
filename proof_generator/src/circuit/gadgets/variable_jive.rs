use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::byte::Byte;

use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;
use franklin_crypto::plonk::circuit::channel::ChannelGadget;
use franklin_crypto::plonk::circuit::channel::JiveChannelGadget;
use franklin_crypto::jive::{JiveEngine, StatefulJive, jive_2_1 as jive_2_1_raw};
use franklin_crypto::plonk::circuit::jive::jive_2_1;

use super::merkle::{MerkleGadget, MerkleCompressor};
use super::utils::digest::{Digest, RawDigest};
use super::utils::num::NumExtension;
use super::utils::pad::multi_rate_pad;
use super::utils::pad::multi_rate_pad_raw;
use super::utils::vec::VarVec;

#[derive(Clone, Debug)]
pub struct JiveGadget<'a, E: JiveEngine> {
    pub params: &'a E::Params
}

pub type RawJiveDigest<E> = RawDigest<E, 1, 32>;
pub type JiveDigest<E> = Digest<E, 1, 32>;

impl<'a, E: JiveEngine> JiveGadget<'a, E> {
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
    ) -> Result<JiveDigest<E>, SynthesisError> {
        let min = input.length().lower();
        let min_input_blocks = (min + Self::BLOCK_SIZE) / Self::BLOCK_SIZE;

        let mut jive = JiveChannelGadget::<E>::new(&self.params);

        let (block_cnt, input_words) = self.pad_and_convert(cs, input)?;
        let mut output = Num::zero();

        for (i, word) in input_words.iter().enumerate() {
            let var = if word.is_constant() {
                AllocatedNum::alloc_cnst(cs, word.get_value().unwrap())?
            } else {
                word.get_variable()
            };
            jive.consume(var, cs)?;
            if i >= min_input_blocks - 1 {
                let possible = Num::Variable(jive.clone().produce_challenge(cs)?);
                let correct = Num::equals(cs, &block_cnt, &Num::Constant(u64_to_ff(i as u64 + 1)))?;
                output = Num::conditionally_select(cs, &correct, &possible, &output)?;
            }
        }
        let words = [output];
        Ok(JiveDigest { words })
    }

    pub fn compress_2_1<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: JiveDigest<E>, y: JiveDigest<E>) -> Result<JiveDigest<E>, SynthesisError> {
        let xv = x.words[0].get_variable();
        let yv = y.words[0].get_variable();
        let words = [Num::Variable(jive_2_1(cs, &xv, &yv, self.params)?)];
        Ok(JiveDigest { words })
    }

    pub fn raw_digest(input: &[u8], params: &'a E::Params) -> RawJiveDigest<E> {
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
        let mut jive = StatefulJive::<E>::new(params);
        jive.absorb(&words);
        let result = jive.squeeze_out_single();
        RawJiveDigest::from_words(&[result])
    }
}

impl<'a, E: JiveEngine> MerkleCompressor<E, 1, 32> for JiveGadget<'a, E> {
    type Params = &'a E::Params;
    fn compress<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: JiveDigest<E>, y: JiveDigest<E>) -> Result<JiveDigest<E>, SynthesisError> {
        self.compress_2_1(cs, x, y)
    }

    fn compress_raw(x: RawJiveDigest<E>, y: RawJiveDigest<E>, params: Self::Params) -> RawJiveDigest<E> {
        let (x,y) = (x.words[0], y.words[0]);
        let words = [jive_2_1_raw::<E>(x, y, params)];
        RawJiveDigest { words }
    }
}

pub type JiveMerkleGadget<'a, E> = MerkleGadget<'a, E, 1, 32, JiveGadget<'a, E>>;

#[cfg(test)]
mod test {
    use super::*;
    use super::super::utils::vec::{VarVecMN, Vecable};
    use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use franklin_crypto::bellman::pairing::bn256::Bn256;
    use franklin_crypto::jive::bn256::Bn256JiveParams;
    use franklin_crypto::plonk::circuit::byte::Byte;

    #[test]
    fn test_jive() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;

        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        let params = Bn256JiveParams::new(true);
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        const M: usize = 500;
        const N: usize = 600;
        let gadget: JiveGadget<E> = JiveGadget::new(&params);
        for _ in 0..200 {
            let len = rng.gen_range(M, N);
            let raw = std::iter::from_fn(|| Some(rng.gen::<u8>())).take(len).collect::<Vec<_>>();
            let input = VarVecMN::<E, Byte<E>, M, N>::alloc(cs, Some(raw.clone())).unwrap();

            let raw_digest = JiveGadget::<E>::raw_digest(raw.as_slice(), &params);
            let digest = gadget.digest(cs, &input).unwrap();
            digest.enforce_equal(cs, &JiveDigest::constant(raw_digest)).unwrap();
        }

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}