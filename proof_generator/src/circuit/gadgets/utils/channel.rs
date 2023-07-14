use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::{Engine, Field, SynthesisError};
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::bellman::pairing::ff::PrimeField;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_exp_to_ff;
use franklin_crypto::plonk::circuit::channel::ChannelGadget;

#[derive(Clone, Debug)]
pub struct AccumulatingChannelGadget<E: Engine, C: ChannelGadget<E>> {
    channel: C,
    accumulator: Num<E>,
    available_bits: u32,
}

impl<E: Engine, C: ChannelGadget<E>> AccumulatingChannelGadget<E, C> {
    pub fn new(params: &C::Params) -> Self {
        let channel = C::new(params);
        let accumulator = Num::zero();
        let available_bits = E::Fr::CAPACITY;
        Self { channel, accumulator, available_bits }
    }

    pub fn consume<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, input: Num<E>, num_bits: u32) -> Result<(), SynthesisError> {
        if self.available_bits >= num_bits {
            // compute accumulator = accumulator * shift + input in one gate
            self.accumulator = Num::fma_with_coefficients(
                cs,
                &self.accumulator,
                &Num::Constant(u64_exp_to_ff(2, num_bits as u64)),
                &input,
                E::Fr::one(),
                E::Fr::one()
            )?;
            self.available_bits -= num_bits;
        } else {
            self.channel.consume(self.accumulator.get_variable(), cs)?;
            self.accumulator = input;
            self.available_bits = E::Fr::CAPACITY - num_bits;
        }
        Ok(())
    }

    pub fn squeeze_challenge<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        // if there's still some pending commitments, consume them
        if self.available_bits != E::Fr::CAPACITY {
            self.channel.consume(self.accumulator.get_variable(), cs)?;
        }
        // produce a challenge
        Ok(Num::Variable(self.channel.produce_challenge(cs)?))
    }
}