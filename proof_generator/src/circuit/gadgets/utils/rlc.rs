use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::bellman::Field;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::channel::{ChannelGadget, RescueChannelGadget, JiveChannelGadget};

use super::bounded::*;
use super::channel::AccumulatingChannelGadget;
use super::range::bit_length;
use super::vec::*;

#[derive(Debug, Copy, Clone)]
pub struct RLC<E: Engine> {
    pub output: Num<E>,
    pub shift: Num<E>
}

#[derive(Debug, Clone)]
pub enum RLCInput<E: Engine> {
    Value(Num<E>, u32),
    Vec(Vec<RLCInput<E>>, BoundedU64<E>),
    Conditional(Boolean, Box<RLCInput<E>>)
}

pub trait Combinable<E: Engine> {
    fn prepare_rlc(&self) -> RLCInput<E>;
}

// impl for &T to workaround rust compiler issue
// where it worries downstream crates could implement Combinable<E> for VarVec<...>,
// causing conflicting implementations
impl<E: Engine, T: Numable<E>> Combinable<E> for &T {
    fn prepare_rlc(&self) -> RLCInput<E> {
        RLCInput::Value(self.to_num(), T::NUM_BITS)
    }
}

// we'd like to write T: Vecable<E> + Cominable<E>, but Combinable may only be impl'd for &T
// where claus is a gross hack to workaround this
impl<E: Engine, T: Vecable<E>> Combinable<E> for VarVec<E, T>
where for<'a> &'a T: Combinable<E> {
    fn prepare_rlc(&self) -> RLCInput<E> {
        RLCInput::Vec(self.vals().iter().map(|v| v.prepare_rlc()).collect(), self.length())
    }
}

impl<E: Engine, T: Combinable<E>> Combinable<E> for &[T] {
    fn prepare_rlc(&self) -> RLCInput<E> {
        RLCInput::Vec(self.iter().map(|v| v.prepare_rlc()).collect(), BoundedU64::constant(self.len()))
    }
}

impl<E: Engine, T: Combinable<E>> Combinable<E> for [&T] {
    fn prepare_rlc(&self) -> RLCInput<E> {
        RLCInput::Vec(self.iter().map(|v| v.prepare_rlc()).collect(), BoundedU64::constant(self.len()))
    }
}

impl<E: Engine, T: Combinable<E>> Combinable<E> for Vec<T> {
    fn prepare_rlc(&self) -> RLCInput<E> {
        self.as_slice().prepare_rlc()
    }
}

impl<E: Engine, T: Combinable<E>, const N: usize> Combinable<E> for [T; N] {
    fn prepare_rlc(&self) -> RLCInput<E> {
        self.as_slice().prepare_rlc()
    }
}

impl<E: Engine> RLCInput<E> {
    fn commit<CS: ConstraintSystem<E>, C: ChannelGadget<E>>(&self, cs: &mut CS, channel: &mut AccumulatingChannelGadget<E, C>) -> Result<(), SynthesisError> {
        match self {
            RLCInput::Value(val, num_bits) => {
                if !val.is_constant() {
                    channel.consume(cs, *val, *num_bits)?;
                }
            },
            RLCInput::Vec(inputs, length) => {
                if !length.to_num().is_constant() {
                    channel.consume(cs, length.to_num(), bit_length(length.upper()) as u32)?;
                }
                for inp in inputs.iter().take(length.upper()) {
                    inp.commit(cs, channel)?;
                }
            },
            RLCInput::Conditional(condition, input) => {
                match condition {
                    Boolean::Is(_) => channel.consume(cs, Num::from_boolean_is(*condition), 1)?,
                    Boolean::Not(_) => {
                        // we make the commitment different for Not vs Is by consuming 2 bits
                        channel.consume(cs, Num::from_boolean_is(condition.not()), 2)?;
                    }
                    Boolean::Constant(_) => (),
                }
                input.commit(cs, channel)?
            }
        }
        Ok(())
    }

    fn compute<CS: ConstraintSystem<E>>(&self, cs: &mut CS, gamma: Num<E>) -> Result<RLC<E>, SynthesisError> {
        match self {
            RLCInput::Value(val, _) => Ok(RLC { output: *val, shift: gamma }),
            RLCInput::Vec(inputs, length) => {
                let mut running = Vec::with_capacity(length.upper());
                let mut output = Num::zero();
                let mut shift = Num::one();
                running.push([output, shift]);

                for inp in inputs.iter().take(length.upper()) {
                    let rlc = inp.compute(cs, gamma)?;

                    // compute output = output * rlc.shift + rlc.output in a single gate
                    output = Num::fma_with_coefficients(
                        cs,
                        &output,
                        &rlc.shift,
                        &rlc.output,
                        E::Fr::one(),
                        E::Fr::one()
                    )?;

                    shift = shift.mul(cs, &rlc.shift)?;
                    running.push([output, shift]);
                }

                let [output, shift] = length.map_multiple(cs, |i| running[i])?;
                Ok(RLC { output, shift })
            },
            RLCInput::Conditional(condition, input) => {
                let RLC { mut output, mut shift } = input.compute(cs, gamma)?;
                output = Num::conditionally_select(cs, condition, &output, &Num::zero())?;
                shift = Num::conditionally_select(cs, condition, &shift, &Num::one())?;
                Ok( RLC { output, shift })
            }
        }
    }
}

pub struct RLCConstraint<E: Engine> {
    left: RLCInput<E>,
    right: RLCInput<E>
}

impl<E: Engine> RLCConstraint<E> {
    pub fn finalize<CS: ConstraintSystem<E>>(&self, cs: &mut CS, gamma: Num<E>) -> Result<(), SynthesisError> {
        let left = self.left.compute(cs, gamma)?;
        let right = self.right.compute(cs, gamma)?;
        left.output.enforce_equal(cs, &right.output)
    }
}

pub struct RLCGadget<E: Engine, C: ChannelGadget<E>> {
    constraints: Vec<RLCConstraint<E>>,
    channel: AccumulatingChannelGadget<E, C>
}

impl<E: Engine, C: ChannelGadget<E>> RLCGadget<E, C> {
    pub fn new(params: &C::Params) -> Self {
        let constraints = Vec::with_capacity(64);
        let channel = AccumulatingChannelGadget::<E, C>::new(params);
        Self { constraints, channel }
    }

    // commits to an RLC constraint
    // the actual constraint is not generated until finalize() is called
    pub fn constrain_rlc<CS: ConstraintSystem<E>, A: Combinable<E>, B: Combinable<E>>(
        &mut self,
        cs: &mut CS,
        a: &A,
        b: &B
    ) -> Result<(), SynthesisError> {
        let left = a.prepare_rlc();
        left.commit(cs, &mut self.channel)?;
        let right = b.prepare_rlc();
        right.commit(cs, &mut self.channel)?;
        self.constraints.push(RLCConstraint { left, right });
        Ok(())
    }

    // finalize all pending RLC constraints
    pub fn finalize<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let gamma = self.channel.squeeze_challenge(cs)?;
        for constraint in &self.constraints {
            constraint.finalize(cs, gamma)?;
        }
        self.constraints = vec![];
        Ok(())
    }
}

impl<E: Engine, C: ChannelGadget<E>> Drop for RLCGadget<E, C> {
    fn drop(&mut self) {
        // panic if the constraints haven't been finalized
        // except for when we're already panicking
        assert!(
            std::thread::panicking() || self.constraints.len() == 0,
            "cannot drop RLCGadget with pending constraints"
        );
    }
}

pub type RescueRLCGadget<E> = RLCGadget<E, RescueChannelGadget<E>>;
pub type JiveRLCGadget<E> = RLCGadget<E, JiveChannelGadget<E>>;

#[cfg(test)]
mod test {
    use super::*;
    use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use franklin_crypto::bellman::pairing::bn256::Bn256;
    use franklin_crypto::rescue::bn256::Bn256RescueParams;
    use franklin_crypto::plonk::circuit::byte::Byte;

    #[test]
    fn test_rlc() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;

        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        let mut params = Bn256RescueParams::new_checked_2_into_1();
        params.set_allow_custom_gate(true);
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        const MIN_LEN: usize = 500;
        const LEN: usize = 600;
        const SPLIT: usize = LEN / 10;
        let mut rlc: RLCGadget<E, RescueChannelGadget<E>> = RLCGadget::new(&params);
        for _ in 0..20 {
            let raw = std::iter::from_fn(|| Some(rng.gen::<u8>())).take(LEN).collect::<Vec<_>>();
            let input = VarVec::<E, Byte<E>>::alloc_with_bounds(cs, Bounds::new(MIN_LEN, LEN), Some(raw.as_slice())).unwrap();
            let split = BoundedU64::alloc(cs, Bounds::new(0, SPLIT), Some(SPLIT)).unwrap();
            let (input0, input1) = input.witness_split(cs, split).unwrap();
            rlc.constrain_rlc(cs, &[input0, input1], &input).unwrap();
        }
        rlc.finalize(cs).unwrap();

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}