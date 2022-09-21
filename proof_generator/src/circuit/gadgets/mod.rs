pub mod merkle;
pub mod variable_keccak;
pub mod header;
pub mod account;
pub mod trie;

use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::bigint_new::constraint_bit_length;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::{Byte, IntoBytes};
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::{ff_to_u64, u64_to_ff};

fn constrain_bit_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    bits: usize
) -> Result<(), SynthesisError> {
    assert!(bits < 64);
    match num {
        Num::Constant(v) => {
            let v = ff_to_u64(v);
            let max = 1 << bits;
            assert!(v < max);
        },
        Num::Variable(var) => {
            if let Some(v) = var.get_value() {
                let v = ff_to_u64(&v);
                let max = 1 << bits;
                assert!(v < max);
            }
            constraint_bit_length(cs, &var, bits)?;
        }
    }
    Ok(())
}

pub trait NumExtension<E: Engine> : Sized {
    fn weighted_sum<CS: ConstraintSystem<E>>(cs: &mut CS, inputs: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>;
    fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError>;
    fn from_be_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError>;
}

impl<E: Engine> NumExtension<E> for Num<E> {
    fn weighted_sum<CS: ConstraintSystem<E>>(cs: &mut CS, inputs: &[Self], base: &E::Fr) -> Result<Self, SynthesisError> {
        let get_value = || {
            let mut cur = E::Fr::zero();
            for val in inputs.iter() {
                cur.mul_assign(base);
                cur.add_assign(&val.get_value().unwrap());
            }
            cur
        };

        if inputs.iter().all(| x | x.is_constant()) {
            Ok(Self::Constant(get_value()))
        } else {
            Ok(Self::Variable(AllocatedNum::alloc(cs, || Ok(get_value()))?))
        }
    }

    fn from_be_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let nums: Vec<Num<E>> = bytes.iter().map(|b| b.into_num()).collect();
        assert!(nums.len() * 8 <= E::Fr::CAPACITY as usize);
        Num::weighted_sum(cs, nums.as_slice(), &E::Fr::from_str("256").unwrap())
    }

    fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let reversed = bytes.into_iter().cloned().rev().collect::<Vec<Byte<E>>>();
        Self::from_be_bytes(cs, reversed.as_slice())
    }
}

#[derive(Clone,Copy)]
pub struct RawDigest<E: Engine, const N: usize> {
    pub words: [E::Fr; N],
}

impl<E: Engine, const N: usize> RawDigest<E, N> {
    pub fn from_words(words: &[E::Fr]) -> Self {
        Self { words: words[..N].try_into().expect("unexpected size") }
    }

    pub fn to_words(&self) -> Vec<E::Fr> {
        self.words.to_vec()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.words.iter().map(ff_to_u64).flat_map(|w| u64::to_le_bytes(w)).collect()
    }

    pub fn parse_digest(words: &[E::Fr]) -> (Self, &[E::Fr]) {
        (Self::from_words(words), &words[N..])
    }
}

impl<E: Engine> RawDigest<E, 4> {
    pub fn from_bytes32(bytes: [u8; 32]) -> Self {
        let words: Vec<E::Fr> = bytes
            .chunks(8)
            .map(|chunk| u64::from_le_bytes(chunk.try_into().expect("unexpected chunk size")))
            .map(u64_to_ff)
            .collect();
        Self { words: words.try_into().expect("unexpected size") }
    }
}

pub struct Digest<E: Engine, const N: usize> {
    pub words: [Num<E>; N],
}

impl<E: Engine, const N: usize> Digest<E, N> {
    pub const NUM_VARIABLES: usize = N;

    fn alloc_impl<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N>>, input: bool) -> Result<Digest<E, N>, SynthesisError> {
        let words = (0..N).map(
            |i| -> Result<_, SynthesisError> {
                let alloc_func = if input { AllocatedNum::alloc_input } else { AllocatedNum::alloc };
                let word = digest.map(|dgst| dgst.words[i]);
                Ok(Num::Variable(alloc_func(cs, || Ok(word.unwrap()))?))
            }
        ).collect::<Result<Vec<_>, _>>()?.try_into().expect("unexpcted digest size");
        Ok(Digest { words })
    }

    pub fn alloc_input<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N>>) -> Result<Digest<E, N>, SynthesisError> {
        Self::alloc_impl(cs, digest, true)
    }

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N>>) -> Result<Digest<E, N>, SynthesisError> {
        Self::alloc_impl(cs, digest, false)
    }

    pub fn get_value(&self) -> Option<RawDigest<E, N>> {
        let vals = self.words.iter().map(|w| w.get_value()).collect::<Option<Vec<_>>>();
        vals.map(|v| RawDigest::from_words(&v))
    }

    pub fn parse_digest_nums(nums: &[Num<E>]) -> (Digest<E, N>, &[Num<E>]) {
        let words = nums[..N].try_into().expect("unexpcted digest size");
        (Digest{ words }, &nums[N..])
    }

    pub fn parse_digest(allocated_nums: &[AllocatedNum<E>]) -> (Digest<E, N>, &[AllocatedNum<E>]) {
        let words = allocated_nums[..N].iter().map(|an| Num::Variable(*an)).collect::<Vec<_>>().try_into().expect("unexpcted digest size");
        (Digest{ words }, &allocated_nums[N..])
    }

    pub fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        for (a, b) in self.words.iter().zip(other.words.iter()) {
            a.enforce_equal(cs, &b)?;
        }
        Ok(())
    }

    pub fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        for (wa, wb) in a.words.iter().zip(b.words.iter()) {
            Num::conditionally_enforce_equal(cs, flag, wa, wb)?;
        }
        Ok(())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        let words = Num::conditionally_select_multiple(cs, flag, &a.words, &b.words)?;
        Ok(Self{ words })
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        let mut result = Boolean::Constant(true);
        for (wa, wb) in a.words.iter().zip(b.words) {
            let eq = Num::equals(cs, &wa, &wb)?;
            result = Boolean::and(cs, &result, &eq)?;
        }
        Ok(result)
    }

    pub fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut bytes = Vec::with_capacity(N*8);
        for w64 in self.words.iter() {
            bytes.extend(w64.into_le_bytes(cs)?.into_iter().take(8));
        }
        Ok(bytes.try_into().expect("unexpected digest size"))
    }

    pub fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let words = bytes.chunks(8).map(
            |chunk| Num::from_le_bytes(cs, chunk)
        ).collect::<Result<Vec<_>, SynthesisError>>()?.try_into().expect("unexpected digest size");
        Ok(Self { words })
    }
}

#[derive(Clone,Copy,Debug)]
pub struct Nibble<E: Engine> {
    byte: Byte<E>,
}

impl<E: Engine> Nibble<E> {
    fn alloc_impl<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>, constrain: bool) -> Result<Self, SynthesisError> {
        if let Some(value) = value {
            assert!(value < 16);
        }

        let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
        if constrain {
            constrain_bit_length(cs, &num, 4)?;
        }
        let byte = Byte::from_num_unconstrained(cs, num);
        Ok(Self { byte })
    }

    pub fn alloc_unconstrained<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, value, false)
    }

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u8>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, value, true)
    }

    pub fn constant(value: u8) -> Self {
        assert!(value < 16);
        Self { byte: Byte::constant(value) }
    }

    pub fn zero() -> Self {
        Self { byte: Byte::zero() }
    }

    pub fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.byte.into_num(), &b.byte.into_num())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        Ok( Self { byte: Byte::conditionally_select(cs, flag, &a.byte, &b.byte)? } )
    }

    pub fn as_byte(&self) -> Byte<E> { self.byte }
}

pub trait ToNibbles<E: Engine, const N: usize> {
    fn to_be_nibbles<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Nibble<E>; N], SynthesisError>;
}

impl<E: Engine> ToNibbles<E, 2> for Byte<E> {
    fn to_be_nibbles<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Nibble<E>; 2], SynthesisError> {
        let value = self.get_byte_value();

        let res = [
            Nibble::alloc(cs, value.map(|v| v >> 4))?,
            Nibble::alloc(cs, value.map(|v| v & 0xf))?,
        ];

        let base = E::Fr::from_str("16").unwrap();
        let elts = &[res[0].as_byte().into_num(), res[1].as_byte().into_num()];
        let num = Num::weighted_sum(cs, elts, &base)?;
        self.into_num().enforce_equal(cs, &num)?;
        Ok(res)
    }
}

pub trait Vecable<E: Engine>: Sized + Clone {
    type Raw: Default;
    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<&Self::Raw>) -> Result<Self, SynthesisError>;
    fn constant(value: &Self::Raw) -> Self;
    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError>;
    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<(), SynthesisError>;
    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError>;
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError>;
    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

impl<E: Engine> Vecable<E> for Byte<E> {
    type Raw = u8;

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<&Self::Raw>) -> Result<Self, SynthesisError> {
        let num = Num::alloc(cs, value.map(|v| u64_to_ff(*v as u64)))?;
        Byte::from_num(cs, num)
    }

    fn constant(value: &Self::Raw) -> Self {
        Byte::constant(*value)
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        self.into_num().enforce_equal(cs, &other.into_num())
    }

    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        Num::conditionally_enforce_equal(cs, flag, &a.into_num(), &b.into_num())
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.into_num(), &b.into_num())
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Byte::<E>::conditionally_select(cs, flag, a, b)
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        match self.into_num() {
            Num::Constant(v) => {
                let inp = Num::alloc(cs, Some(v))?;
                self.into_num().enforce_equal(cs, &inp)?;
                inp.inputize(cs)
            }
            Num::Variable(var) => {
                var.inputize(cs)
            }
        }
    }
}

impl<E: Engine> Vecable<E> for Num<E> {
    type Raw = u64;

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<&Self::Raw>) -> Result<Self, SynthesisError> {
        Num::alloc(cs, value.map(|v| u64_to_ff(*v)))
    }

    fn constant(value: &Self::Raw) -> Self {
        Num::Constant(u64_to_ff(*value))
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        Num::enforce_equal(self, cs, other)
    }

    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        Num::conditionally_enforce_equal(cs, flag, a, b)
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a, &b)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Num::<E>::conditionally_select(cs, flag, a, b)
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.get_variable().inputize(cs)
    }
}

impl<E: Engine> Vecable<E> for Nibble<E> {
    type Raw = u8;

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<&Self::Raw>) -> Result<Self, SynthesisError> {
        Nibble::alloc(cs, value.map(|v| *v))
    }

    fn constant(value: &Self::Raw) -> Self {
        Nibble::constant(*value)
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        self.as_byte().enforce_equal(cs, &other.as_byte())
    }

    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        Byte::conditionally_enforce_equal(cs, flag, &a.byte, &b.byte)
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Nibble::equals(cs, a, b)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Nibble::conditionally_select(cs, flag, a, b)
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.as_byte().into_num().get_variable().inputize(cs)
    }
}

#[derive(Clone, Copy)]
pub struct VarVec<E: Engine, T: Vecable<E> + Copy, const N: usize> {
    length: Num<E>,
    vals: [T; N],
}

impl<E: Engine, T: Vecable<E> + Copy, const N: usize> VarVec<E, T, N> {
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: Option<&[T::Raw]>
    ) -> Result<Self, SynthesisError> {
        let length = values.map(|vals| vals.len());
        let default = &T::Raw::default();
        let mut vals = [T::constant(default); N];
        for i in 0..N {
            vals[i] = T::alloc(cs, values.map(|vals| vals.get(i).unwrap_or(&default)))?;
        }

        if let Some(length) = length {
            assert!(length <= N);
        }
        let length = Num::alloc(cs, length.map(|l| u64_to_ff(l as u64)))?;
        Ok(Self { length, vals })
    }

    pub fn from(values: &[T]) -> Self {
        let length = values.len();
        assert!(length <= N);

        let default = &T::Raw::default();
        let mut vals = [T::constant(default); N];
        for i in 0..length {
            vals[i] = values[i];
        }

        let length = Num::Constant(u64_to_ff(length as u64));
        Self { length, vals }
    }

    pub fn get<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        idx: Num<E>
    ) -> Result<T, SynthesisError> {
        let mut result = T::constant(&T::Raw::default());
        match idx {
            Num::Constant(idx) => {
                result = self.vals[ff_to_u64(&idx) as usize];
            },
            Num::Variable(_) => {
                for i in 0..N {
                    let is_idx = Num::equals(cs, &idx, &Num::Constant(u64_to_ff(i as u64)))?;
                    result = T::conditionally_select(cs, &is_idx, &self.vals[i], &result)?;
                }
            }
        }
        Ok(result)
    }

    // variable slice, for concrete slice just use .vals[..]
    pub fn slice<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        start: Num<E>,
        end: Num<E>
    ) -> Result<Self, SynthesisError> {
        let default = &T::Raw::default();
        let mut vals = [T::constant(default); N];
        let length: Num<E>;

        match (start, end) {
            (Num::Constant(start_const), Num::Constant(end_const)) => {
                let (start, end) = (ff_to_u64(&start_const) as usize, ff_to_u64(&end_const) as usize);
                assert!(end >= start);
                assert!(end <= N);
                let len = end - start;
                for i in 0..len {
                    vals[i] = self.vals[start+i];
                }
                length = Num::Constant(u64_to_ff(len as u64));
            },
            (Num::Constant(start_const), Num::Variable(_)) => {
                length = end.sub(cs, &start)?;

                let start = ff_to_u64(&start_const) as usize;
                assert!(start <= N);
                for i in 0..N-start {
                    vals[i] = self.vals[start+i];
                }
            },
            (Num::Variable(_), Num::Constant(end_const)) => {
                length = end.sub(cs, &start)?;

                let end = ff_to_u64(&end_const) as usize;
                for si in 0..end {
                    let idx = Num::Constant(u64_to_ff(si as u64));
                    let is_start = &Num::equals(cs, &start, &idx)?;
                    for i in 0..end-si {
                        vals[i] = T::conditionally_select(
                            cs,
                            &is_start,
                            &self.vals[i+si],
                            &vals[i]
                        )?;
                    }
                }
            }
            (Num::Variable(_), Num::Variable(_)) => {
                length = end.sub(cs, &start)?;

                for si in 0..N {
                    let idx = Num::Constant(u64_to_ff(si as u64));
                    let is_start = &Num::equals(cs, &start, &idx)?;
                    for i in 0..N-si {
                        vals[i] = T::conditionally_select(
                            cs,
                            &is_start,
                            &self.vals[i+si],
                            &vals[i]
                        )?;
                    }
                }
            }
        }

        Ok(Self { length, vals })
    }

    pub fn suffix<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        start: Num<E>,
        hint_max: Option<usize>,
    ) -> Result<Self, SynthesisError> {
        match hint_max {
            Some(max) => {
                let mut result = Self::constant(&vec![]);
                for i in 0..=max {
                    let idx = Num::Constant(u64_to_ff(i as u64));
                    let start_is_i = Num::equals(cs, &start, &idx)?;
                    let suffix_i = self.slice(cs, idx, self.length)?;
                    result = Self::conditionally_select(cs, &start_is_i, &suffix_i, &result)?;
                }
                Ok(result)
            },
            None => self.slice(cs, start, self.length)
        }
    }

    pub fn starts_with<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Boolean, SynthesisError> {
        let mut equal = Boolean::Constant(true);
        let mut reached_end = Boolean::Constant(false);
        for i in 0..N {
            let idx = Num::Constant(u64_to_ff(i as u64));
            let end_self = Num::equals(cs, &idx, &self.length)?;
            let end_other = Num::equals(cs, &idx, &other.length)?;
            reached_end = Boolean::or(cs, &reached_end, &end_other)?;

            let lengths_ok = Boolean::or(cs, &reached_end, &end_self.not())?;
            equal = Boolean::and(cs, &equal, &lengths_ok)?;

            let val_eq = T::equals(cs, &self.vals[i], &other.vals[i])?;
            let i_result = Boolean::or(cs, &val_eq, &reached_end)?;
            equal = Boolean::and(cs, &equal, &i_result)?;
        }
        Ok(equal)
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        let mut equal = Num::equals(cs, &a.length(), &b.length())?;
        let length = a.length();
        let mut reached_end = Boolean::Constant(false);
        for i in 0..N {
            let idx = Num::Constant(u64_to_ff(i as u64));
            let end = Num::equals(cs, &idx, &length)?;
            reached_end = Boolean::or(cs, &reached_end, &end)?;

            let val_eq = T::equals(cs, &a.vals[i], &b.vals[i])?;
            let i_result = Boolean::or(cs, &val_eq, &reached_end)?;
            equal = Boolean::and(cs, &equal, &i_result)?;
        }
        Ok(equal)
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.length.get_variable().inputize(cs)?;
        for i in 0..N {
            self.vals[i].inputize(cs)?;
        }
        Ok(())
    }

    pub fn length(&self) -> Num<E> { self.length }
    pub fn vals(&self) -> &[T; N] { &self.vals }
}

impl<E: Engine, T: Vecable<E> + Copy, const N: usize> Vecable<E> for VarVec<E, T, N> {
    type Raw = Vec<T::Raw>;

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<&Self::Raw>) -> Result<Self, SynthesisError> {
        VarVec::alloc(cs, value.map(Vec::as_slice))
    }

    fn constant(value: &Self::Raw) -> Self {
        let length = Num::Constant(u64_to_ff(value.len() as u64));
        let mut vals = [T::constant(&T::Raw::default()); N];
        for (i, v) in value.iter().enumerate() {
            vals[i] = T::constant(v);
        }
        Self { length, vals }
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        for (a, b) in self.vals.iter().zip(other.vals.iter()) {
            a.enforce_equal(cs, &b)?;
        }
        Ok(())
    }

    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        for (av, bv) in a.vals.iter().zip(b.vals.iter()) {
            T::conditionally_enforce_equal(cs, flag, av, bv)?;
        }
        Ok(())
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        VarVec::equals(cs, &a, &b)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        let length = Num::conditionally_select(cs, flag, &a.length(), &b.length())?;
        let mut vals = [T::constant(&T::Raw::default()); N];
        for i in 0..N {
            vals[i] = T::conditionally_select(cs, flag, &a.vals[i], &b.vals[i])?;
        }

        Ok( Self { length, vals })
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        VarVec::inputize(&self, cs)
    }
}

impl<E: Engine, T: Vecable<E> + Copy, const N: usize> From<[T; N]> for VarVec<E, T, N> {
    fn from(vals: [T; N]) -> Self {
        let length = Num::Constant(u64_to_ff(N as u64));
        Self { length, vals }
    }
}
