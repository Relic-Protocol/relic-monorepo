use std::marker::PhantomData;

use franklin_crypto::bellman::{Engine, SynthesisError};
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

use super::rlc::{Combinable, RLCInput};
use super::bounded::{Bounds, BoundedU64};
use super::vec::*;
use super::range::*;

pub struct RLPGadget<E: Engine>(
    // TODO
    PhantomData<E>
);

pub struct RLPDataResult<E: Engine>  {
    pub exists: Boolean,
    prefix: VarVec<E, Byte<E>>,
    pub data: VarVec<E, Byte<E>>,
    rest: VarVec<E, Byte<E>>
}

impl<E: Engine> Combinable<E> for RLPDataResult<E> {
    fn prepare_rlc(&self) -> RLCInput<E> {
        let mut vec = Vec::with_capacity(3);
        vec.push(self.prefix.prepare_rlc());
        vec.push(self.data.prepare_rlc());
        vec.push(self.rest.prepare_rlc());
        let inner = RLCInput::Vec(vec, BoundedU64::constant(3));
        RLCInput::Conditional(self.exists, Box::new(inner))
    }
}

pub struct RLPListResult<E: Engine> {
    prefix: VarVec<E, Byte<E>>,
    pub field_results: Vec<RLPDataResult<E>>,
    rest: VarVec<E, Byte<E>>
}

impl<E: Engine> Combinable<E> for RLPListResult<E> {
    fn prepare_rlc(&self) -> RLCInput<E> {
        let mut vec = Vec::with_capacity(self.field_results.len() + 2);
        vec.push(self.prefix.prepare_rlc());
        for field in self.field_results.iter() {
            vec.push(field.prepare_rlc());
        }
        vec.push(self.rest.prepare_rlc());
        let len = vec.len();
        RLCInput::Vec(vec, BoundedU64::constant(len))
    }
}

fn length_encoding_length(len: usize) -> usize {
    if len <= 55 { 0 } else { byte_length(len) }
}

fn length_encoding_bounds(bounds: Bounds) -> Bounds {
    Bounds::new(length_encoding_length(bounds.lower), length_encoding_length(bounds.upper))
}

fn field_encoding_bounds(field_bounds: Bounds) -> (Bounds, Bounds) {
    let len_bounds = length_encoding_bounds(field_bounds);

    // If we know the field is at least 2 bytes long,
    // then we know there's going to be exactly one prefix byte.
    // Otherwise, it could possibly be a 1 byte value and not have a prefix byte.
    let prefix_byte_bounds = if field_bounds.lower > 1 { Bounds::new(1, 1) } else { Bounds::new(0, 1) };

    let prefix_bounds = len_bounds.add(prefix_byte_bounds);
    (len_bounds, prefix_bounds)
}

fn list_data_bounds(field_bounds: &[Bounds]) -> Bounds {
    let mut result = Bounds::new(0, 0);
    for &field_bounds in field_bounds {
        let (_, prefix_bounds) = field_encoding_bounds(field_bounds);
        result = result.add(prefix_bounds).add(field_bounds);
    }
    result
}

fn list_encoding_bounds(fields: &[Bounds], extra: &[Bounds]) -> (Bounds, Bounds, Bounds) {
    let mut data_bounds = list_data_bounds(fields);
    let extra_bounds = list_data_bounds(extra);
    data_bounds = data_bounds.add(Bounds::new(0, extra_bounds.upper));
    let len_bounds = length_encoding_bounds(data_bounds);
    let prefix_bounds = len_bounds.add_const(1);
    (len_bounds, prefix_bounds, data_bounds)
}

pub fn encoded_list_bounds(fields: &[Bounds], extra: &[Bounds]) -> Bounds {
    let (_, prefix_bounds, data_bounds) = list_encoding_bounds(fields, extra);
    prefix_bounds.add(data_bounds)
}

// A low-level RLP parsing gadget. The returned data is not fully
// constrained until checked with RLC, so this must be used with care.
// Parses RLP data according to predefined field size bounds,
// by splitting the input string into (prefix || data || rest)
// where |prefix| contains the prefix byte and encoded length (if any),
// |data| contains the actual field data, and |rest| contains the remaining
// input bytes.
// NOTE: the returned slices only have their lengths constrained.
// The data must be constrained by checking RLC(input) == RLC(parse_result)
impl<E: Engine> RLPGadget<E> {
    pub fn new() -> Self { Self(PhantomData) }

    fn default_encoded(field_bounds: Bounds) -> VarVec<E, Byte<E>> {
        let len = field_bounds.lower;
        let value = std::iter::repeat(0x0).take(len);
        let vec = if len == 1 {
            std::iter::empty().chain(value).collect()
        } else if len <= 55 {
            std::iter::once(0x80 + (len as u8)).chain(value).collect()
        } else {
            std::iter::once(0xf7 + (byte_length(len) as u8)).chain(value).collect()
        };
        VarVec::constant(vec)
    }

    pub fn parse_list_data<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        list_bounds: Bounds,
        inp: &VarVec<E, Byte<E>>
    ) -> Result<RLPDataResult<E>, SynthesisError> {
        // determine the bounds for the parsed list
        let len_bounds = Bounds::new(length_encoding_length(list_bounds.lower), length_encoding_length(list_bounds.upper));

        // look at first byte
        let prefix_byte = inp.vals()[0];

        // check we're looking at a list
        check_greater_or_equal_usize(cs, &prefix_byte.inner, 8, 0xc0)?;

        let is_short = BoundedU64::from_byte(cs, prefix_byte)?.is_less_or_equal(cs, 0xf7)?;

        // field length if the list is short, else 0
        let short_len = prefix_byte
            .to_num()
            .sub(cs, &Num::Constant(u64_to_ff(0xc0)))?
            .mul(cs, &Num::from_boolean_is(is_short))?;

        // otherwise the list is long
        // note that we allocate a new bool so that we can use Num::from_boolean_is
        let is_long = Boolean::alloc(cs, is_short.not().get_value())?;
        Boolean::enforce_equal(cs, &is_long, &is_short.not())?;

        // len_len is 0 if field is a literal or short length
        let len_len = prefix_byte
            .to_num()
            .sub(cs, &Num::Constant(u64_to_ff(0xf7)))?
            .mul(cs, &Num::from_boolean_is(is_long))?;

        let bounded_len_len = BoundedU64::from(cs, len_len, len_bounds)?;

        // field length if the field is long, else 0
        let long_len = inp
            .suffix(cs, 1)?
            .resize(bounded_len_len)
            .weighted_sum(cs, u64_to_ff(256))?;

        let data_len = short_len.add(cs, &long_len)?;

        let bounded_prefix_len = bounded_len_len.add_const(cs, 1)?;
        let bounded_data_len = BoundedU64::from(cs, data_len, list_bounds)?;

        // split string into 3 slices: inp == prefix || data || rest
        let (prefix, rest) = inp.witness_split(cs, bounded_prefix_len)?;
        let (data, rest) = rest.witness_split(cs, bounded_data_len)?;
        let exists = Boolean::Constant(true);

        Ok(RLPDataResult { exists, prefix, data, rest })
    }

    // TOOD: optimize for when field_bounds is a constant, i.e. the field is fixed-size
    pub fn parse_field_data<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        field_bounds: Bounds,
        inp: &VarVec<E, Byte<E>>
    ) -> Result<RLPDataResult<E>, SynthesisError> {
        // determine the bounds for the parsed fields
        let (len_bounds, prefix_bounds) = field_encoding_bounds(field_bounds);

        // look at first byte
        let prefix_byte = inp.vals()[0];
        let bits = prefix_byte.inner.get_variable().into_bits_le(cs, Some(8))?;
        
        // field is a literal iff prefix_byte < 0x80
        let is_not_literal = bits[7];

        // check if field is short (<= 55 bytes)
        let mut is_short = BoundedU64::from_byte(cs, prefix_byte)?.is_less_or_equal(cs, 0xb7)?;
        is_short = Boolean::and(cs, &is_short, &is_not_literal)?;

        // otherwise the field is long
        let is_long = Boolean::and(cs, &is_short.not(), &is_not_literal)?;

        // len_len is 0 if field is a literal or short length
        let len_len = prefix_byte
            .to_num()
            .sub(cs, &Num::Constant(u64_to_ff(0xb7)))?
            .mul(cs, &Num::from_boolean_is(is_long))?;

        // 0 if field is a literal, otherwise 1 + len_len
        let prefix_len = Num::from_boolean_is(is_not_literal).add(cs, &len_len)?;

        // field length if the field is a literal, else 0
        let literal_field_len = Num::one().sub(cs, &Num::from_boolean_is(is_not_literal))?;

        // field length if the field is short, else 0
        let short_len = prefix_byte
            .to_num()
            .sub(cs, &Num::Constant(u64_to_ff(0x80)))?
            .mul(cs, &Num::from_boolean_is(is_short))?;

        // constrain len_len with the known bounds
        let bounded_len_len = BoundedU64::from(cs, len_len, len_bounds)?;

        // field length if the field is long, else 0
        let long_len = inp
            .suffix(cs, 1)?
            .resize(bounded_len_len)
            .weighted_sum(cs, u64_to_ff(256))?;

        let field_len = literal_field_len.add(cs, &short_len)?.add(cs, &long_len)?;

        // constrain prefix_len and field_len with the known bounds
        let bounded_prefix_len = BoundedU64::from(cs, prefix_len, prefix_bounds)?;
        let bounded_field_len = BoundedU64::from(cs, field_len, field_bounds)?;

        // split string into 3 slices: inp == prefix || data || rest
        let (prefix, rest) = inp.witness_split(cs, bounded_prefix_len)?;
        let (data, rest) = rest.witness_split(cs, bounded_field_len)?;
        let exists = Boolean::Constant(true);

        Ok(RLPDataResult { exists, prefix, data, rest })
    }

    pub fn parse_extra_field_data<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        field_bounds: Bounds,
        inp: &VarVec<E, Byte<E>>
    ) -> Result<RLPDataResult<E>, SynthesisError> {
        // TODO: improve this
        // The current version conditionally replaces the input if it
        // doesn't exist to avoid synthesis failures in range checks
        // We should theoretically be able to parse even with bad input
        let missing = inp.length().to_num().is_zero(cs)?;
        let default = Self::default_encoded(field_bounds);
        let parseable = VarVec::conditionally_select(cs, &missing, &default, inp)?;
        let mut result = self.parse_field_data(cs, field_bounds, &parseable)?;
        result.exists = missing.not();
        Ok(result)
    }

    // TODO: implement parsing list fields that are lists
    pub fn parse_list<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        fields: &[Bounds],
        extra: &[Bounds],
        inp: &VarVec<E, Byte<E>>
    ) -> Result<RLPListResult<E>, SynthesisError> {
        let (_, _, data_bounds) = list_encoding_bounds(fields, extra);
        let list_data = self.parse_list_data(cs, data_bounds, inp).unwrap();

        let mut data = list_data.data;
        let mut field_results = Vec::with_capacity(fields.len());

        for &field in fields {
            let mut field_result = self.parse_field_data(cs, field, &data)?;
            data = field_result.rest;
            field_result.rest = VarVec::from(&[]);
            field_results.push(field_result);
        }

        for &field in extra {
            let mut field_result = self.parse_extra_field_data(cs, field, &data)?;
            data = field_result.rest;
            field_result.rest = VarVec::from(&[]);
            field_results.push(field_result);
        }

        let prefix = list_data.prefix;
        let rest = list_data.rest;
        Ok(RLPListResult { prefix, field_results, rest})
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use franklin_crypto::plonk::circuit::channel::RescueChannelGadget;
    use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use franklin_crypto::bellman::pairing::bn256::Bn256;
    use franklin_crypto::rescue::bn256::Bn256RescueParams;
    use super::super::rlc::RLCGadget;
    use ::rlp::encode_list;

    #[test]
    fn test_rlp() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;
        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        let mut params = Bn256RescueParams::new_checked_2_into_1();
        params.set_allow_custom_gate(true);
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut rlc: RLCGadget<E, RescueChannelGadget<E>> = RLCGadget::new(&params);
        for _ in 0..100 {
            let num_fields = rng.gen_range(0, 20);
            let field_bounds = std::iter::from_fn(|| {
                let lower = rng.gen_range(0, 32);
                let upper = rng.gen_range(lower, 128);
                Some(Bounds::new(lower, upper))
            }).take(num_fields).collect::<Vec<_>>();

            let num_extra = rng.gen_range(0, 4);
            let extra_bounds = std::iter::from_fn(|| {
                let lower = rng.gen_range(0, 32);
                let upper = rng.gen_range(lower, 128);
                Some(Bounds::new(lower, upper))
            }).take(num_extra).collect::<Vec<_>>();

            let (_, prefix_bounds, fields_bounds) = list_encoding_bounds(&field_bounds, &extra_bounds);
            let encoded_list_bounds = prefix_bounds.add(fields_bounds);

            let actual_extra = rng.gen_range(0, num_extra+1);
            let fields_raw = field_bounds.iter().chain(extra_bounds.iter().take(actual_extra)).map(|b| {
                let len: usize = rng.gen_range(b.lower, b.upper+1);
                std::iter::from_fn(|| Some(rng.gen::<u8>())).take(len).collect::<Vec<_>>()
            }).collect::<Vec<_>>();

            let encoded = encode_list::<Vec<u8>, _>(&fields_raw);
            let input = VarVec::<E, Byte<E>>::alloc_with_bounds(cs, encoded_list_bounds, Some(&encoded)).unwrap();
            let rlp: RLPGadget<E> = RLPGadget::new();

            let result = rlp.parse_list(cs, &field_bounds, &extra_bounds, &input).unwrap();
            let bounds_iter = field_bounds.iter().chain(extra_bounds.iter());
            for (i, ((&bound, field_result), field_value)) in bounds_iter.zip(result.field_results.iter()).zip(fields_raw.iter()).enumerate() {
                // check against expected parsing
                assert!(field_result.exists.get_value().unwrap() == (i < num_fields + actual_extra));
                assert!(field_result.data.length().bounds() == bound);
                assert!(field_result.data.get_value().unwrap() == *field_value);
            }
            assert!(result.rest.length().get_value().unwrap() == 0);

            // queue up an rlc constraint
            rlc.constrain_rlc(cs, &result, &input).unwrap();
        }

        // finalize all rlp constraints
        rlc.finalize(cs).unwrap();

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}