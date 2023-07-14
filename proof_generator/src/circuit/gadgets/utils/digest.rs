
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::{Engine, SynthesisError};
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::{ff_to_u64, u64_to_ff};

use crate::circuit::gadgets::utils::vec::Numable;

use super::vec::Vecable;
use super::num::NumExtension;

#[derive(Clone, Copy)]
pub struct RawDigest<E: Engine, const N: usize, const M: usize> {
    pub words: [E::Fr; N],
}

impl<E: Engine, const N: usize, const M: usize> RawDigest<E, N, M> {
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

    pub fn from_bytes<const K: usize>(bytes: [u8; K]) -> Self {
        assert_eq!(K, N * M);
        let words: Vec<E::Fr> = bytes
            .chunks(M)
            .map(|chunk| u64::from_le_bytes(chunk.try_into().expect("unexpected chunk size")))
            .map(u64_to_ff)
            .collect();
        Self { words: words.try_into().expect("unexpected size") }
    }

    pub fn to_byte_digest<const K: usize>(&self) -> RawDigest<E, K, 1> {
        let vec = self.to_bytes().iter().map(|b| u64_to_ff(*b as u64)).collect::<Vec<_>>();
        let words = vec.try_into().expect("array size");
        RawDigest{ words }
    }
}

#[derive(Debug, Clone)]
pub struct Digest<E: Engine, const N: usize, const M: usize> {
    pub words: [Num<E>; N],
}

impl<E: Engine, const N: usize, const M: usize> Digest<E, N, M> {
    pub const NUM_VARIABLES: usize = N;

    pub fn constant(raw: RawDigest<E, N, M>) -> Digest<E, N, M> {
        let words = raw.words.map(Num::Constant);
        Self { words }
    }

    fn alloc_impl<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N, M>>, input: bool) -> Result<Digest<E, N, M>, SynthesisError> {
        let words = (0..N).map(
            |i| -> Result<_, SynthesisError> {
                let alloc_func = if input { AllocatedNum::alloc_input } else { AllocatedNum::alloc };
                let word = digest.map(|dgst| dgst.words[i]);
                Ok(Num::Variable(alloc_func(cs, || Ok(word.unwrap()))?))
            }
        ).collect::<Result<Vec<_>, _>>()?.try_into().expect("unexpcted digest size");
        Ok(Digest { words })
    }

    pub fn alloc_input<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N, M>>) -> Result<Digest<E, N, M>, SynthesisError> {
        Self::alloc_impl(cs, digest, true)
    }

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, digest: Option<RawDigest<E, N, M>>) -> Result<Digest<E, N, M>, SynthesisError> {
        Self::alloc_impl(cs, digest, false)
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        for word in self.words {
            word.inputize(cs)?;
        }
        Ok(())
    }

    pub fn get_value(&self) -> Option<RawDigest<E, N, M>> {
        let vals = self.words.iter().map(|w| w.get_value()).collect::<Option<Vec<_>>>();
        vals.map(|v| RawDigest::from_words(&v))
    }

    pub fn parse_digest_nums(nums: &[Num<E>]) -> (Digest<E, N, M>, &[Num<E>]) {
        let words = nums[..N].try_into().expect("unexpcted digest size");
        (Digest{ words }, &nums[N..])
    }

    pub fn parse_digest(allocated_nums: &[AllocatedNum<E>]) -> (Digest<E, N, M>, &[AllocatedNum<E>]) {
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
        let mut bytes = Vec::with_capacity(N*M);
        for wm in self.words.iter() {
            let nums = wm.split_into_fixed_number_of_limbs(cs, 8, M)?;
            bytes.extend(nums.iter().map(|num| Byte { inner: *num }));
        }
        Ok(bytes.try_into().expect("unexpected digest size"))
    }

    pub fn from_le_bytes<CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Result<Self, SynthesisError> {
        let words = bytes.chunks(M).map(
            |chunk| Num::from_le_bytes(cs, chunk)
        ).collect::<Result<Vec<_>, SynthesisError>>()?.try_into().expect("unexpected digest size");
        Ok(Self { words })
    }

    pub fn to_byte_digest<CS: ConstraintSystem<E>, const K: usize>(&self, cs: &mut CS) -> Result<Digest<E, K, 1>, SynthesisError> {
        assert_eq!(K, N * M);
        let vec = self.into_le_bytes(cs)?.iter().map(|w| w.to_num()).collect::<Vec<_>>();
        let words = vec.try_into().expect("array size");
        Ok(Digest{ words })
    }
}

pub trait Hasher<E: Engine> {
    type Params: Clone;
    fn hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &[Byte<E>]) -> Result<Vec<Byte<E>>, SynthesisError>;
    fn raw_hash(input: &[u8], params: Self::Params) -> Vec<u8>;
}