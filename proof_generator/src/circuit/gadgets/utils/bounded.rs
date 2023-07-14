use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::{ff_to_u64, u64_to_ff};
use franklin_crypto::bellman::{Field,PrimeField};

use super::range::*;
use super::vec::*;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Bounds {
    pub lower: usize,
    pub upper: usize 
}

impl Bounds {
    pub const fn new(lower: usize, upper: usize) -> Self {
        assert!(lower <= upper);
        Self { lower, upper }
    }

    // returns new bounds and whether we need to constrain the result to the bound
    pub const fn add_with_check(&self, other: Self) -> (Self, bool) {
        let (lower, check) = if self.lower > usize::MAX - other.lower {
            (usize::MAX, true)
        } else {
            (self.lower + other.lower, false)
        };
        let (upper, check) = if self.upper > usize::MAX - other.upper {
            (usize::MAX, true)
        } else {
            (self.upper + other.upper, check)
        };
        (Self { lower, upper }, check)
    }

    pub const fn add(&self, other: Self) -> Self {
        let (result, check) = self.add_with_check(other);
        assert!(!check);
        result
    }

    // returns new bounds and whether we need to constrain the result to the bound
    pub const fn sub(&self, other: Self) -> (Self, bool) {
        assert!(self.upper >= other.lower);
        let (lower, check) = if self.lower >= other.upper {
           (self.lower - other.upper, false)
        } else {
            (0, true)
        };
        let upper = self.upper - other.lower;
        (Self { lower, upper }, check)
    }

    // returns new bounds and whether we need to constrain the result to the bound
    pub const fn add_const_with_check(&self, c: usize) -> (Self, bool) {
        let (lower, check) = if self.lower > usize::MAX - c {
            (usize::MAX, true)
        } else {
            (self.lower + c, false)
        };
        let (upper, check) = if self.upper > usize::MAX - c {
            (usize::MAX, true)
        } else {
            (self.upper + c, check)
        };
        (Self { lower, upper }, check)
    }

    pub const fn add_const(&self, c: usize) -> Self {
        let (result, check) = self.add_const_with_check(c);
        assert!(!check);
        result
    }

    // returns new bounds and whether we need to constrain the result to the bound
    pub const fn sub_const(&self, c: usize) -> (Self, bool) {
        assert!(self.upper >= c);
        let (lower, check) = if self.lower >= c {
            (self.lower - c, false)
        } else {
            (0, true)
        };
        let upper = self.upper - c;
        (Self { lower, upper }, check)
    }

    pub fn union(&self, other: Self) -> Self {
        let lower = usize::min(self.lower, other.lower);
        let upper = usize::max(self.upper, other.upper);
        Self { lower, upper }
    }

    pub const fn includes(&self, other: Self) -> bool {
        self.lower <= other.lower && self.upper >= other.upper
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BoundedU64<E: Engine> {
    num: Num<E>,
    bounds: Bounds
}

impl<E: Engine> BoundedU64<E> {
    const MAX_MAP_RANGE: usize = 65536;

    fn from_impl<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>, bounds: Bounds, constrain: bool) -> Result<Self, SynthesisError> {
        if constrain {
            check_greater_or_equal_usize(cs, &num, bit_length(bounds.upper), bounds.lower)?;
            check_less_or_equal_usize(cs, &num, bounds.upper)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn to_num(&self) -> Num<E> {
        self.num
    }

    pub fn bounds(&self) -> Bounds {
        self.bounds
    }

    pub fn upper(&self) -> usize {
        self.bounds.upper
    }

    pub fn lower(&self) -> usize {
        self.bounds.lower
    }

    pub fn from_unconstrained<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>, bounds: Bounds) -> Result<Self, SynthesisError> {
        Self::from_impl(cs, num, bounds, false)
    }

    pub fn from<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>, bounds: Bounds) -> Result<Self, SynthesisError> {
        Self::from_impl(cs, num, bounds, true)
    }

    pub fn alloc_impl<CS: ConstraintSystem<E>>(cs: &mut CS, bounds: Bounds, value: Option<usize>, constrain: bool) -> Result<Self, SynthesisError> {
        let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
        Self::from_impl(cs, num, bounds, constrain)
    }

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, bounds: Bounds, value: Option<usize>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, bounds, value, true)
    }

    pub fn alloc_unconstrained<CS: ConstraintSystem<E>>(cs: &mut CS, bounds: Bounds, value: Option<usize>) -> Result<Self, SynthesisError> {
        Self::alloc_impl(cs, bounds, value, false)
    }

    pub fn from_byte<CS: ConstraintSystem<E>>(cs: &mut CS, byte: Byte<E>) -> Result<Self, SynthesisError> {
        Self::from_impl(cs, byte.to_num(), Bounds::new(0, 255), false)
    }

    pub fn constant(val: usize) -> Self {
        let num = Num::Constant(u64_to_ff(val as u64));
        let bounds = Bounds::new(val, val);
        Self { num, bounds }
    }

    pub fn get_value(&self) -> Option<usize> {
        self.num.get_value().map(|v| ff_to_u64(&v) as usize)
    }

    pub fn get_variable(&self) -> AllocatedNum<E> {
        self.num.get_variable()
    }

    pub fn change_bounds<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bounds: Bounds) -> Result<Self, SynthesisError> {
        let num = self.num;
        if bounds.lower > self.bounds.lower {
            check_greater_or_equal_usize(cs, &num, bit_length(bounds.upper), bounds.lower)?;
        }
        if bounds.upper < self.bounds.upper {
            check_less_or_equal_usize(cs, &num, bounds.upper)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn change_upper<CS: ConstraintSystem<E>>(&self, cs: &mut CS, upper: usize) -> Result<Self, SynthesisError> {
        self.change_bounds(cs, Bounds::new(self.bounds.lower, upper))
    }

    pub fn change_lower<CS: ConstraintSystem<E>>(&self, cs: &mut CS, lower: usize) -> Result<Self, SynthesisError> {
        self.change_bounds(cs, Bounds::new(lower, self.bounds.upper))
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let num = self.num.add(cs, &other.num)?;
        let (bounds, check) = self.bounds.add_with_check(other.bounds);
        if check {
            constrain_bit_length(cs, &num, 64)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let num = self.num.sub(cs, &other.num)?;
        let (bounds, check) = self.bounds.sub(other.bounds);
        if check {
            constrain_bit_length(cs, &num, 64)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn add_const<CS: ConstraintSystem<E>>(&self, cs: &mut CS, c: usize) -> Result<Self, SynthesisError> {
        let num = self.num.add(cs, &Num::Constant(u64_to_ff(c as u64)))?;
        let (bounds, check) = self.bounds.add_const_with_check(c);
        if check {
            constrain_bit_length(cs, &num, 64)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn sub_const<CS: ConstraintSystem<E>>(&self, cs: &mut CS, c: usize) -> Result<Self, SynthesisError> {
        let num = self.num.sub(cs, &Num::Constant(u64_to_ff(c as u64)))?;
        let (bounds, check) = self.bounds.sub_const(c);
        if check {
            constrain_bit_length(cs, &num, 64)?;
        }
        Ok(Self { num, bounds })
    }

    pub fn map_multiple<CS: ConstraintSystem<E>, T: Vecable<E>, const N: usize, F: Fn (usize) -> [T; N]>(
        &self,
        cs: &mut CS,
        f: F
    ) -> Result<[T; N], SynthesisError> {
        assert!(self.bounds.upper - self.bounds.lower <= Self::MAX_MAP_RANGE);
        let default = T::constant(T::Raw::default());
        match self.num {
            Num::Constant(v) => Ok(f(ff_to_u64(&v) as usize)),
            Num::Variable(_) => {
                let mut result = [(); N].map(|_| default.clone());
                for v in self.bounds.lower..=self.bounds.upper {
                    let condition = Num::equals(cs, &self.num, &Num::Constant(u64_to_ff(v as u64)))?;
                    let vals = f(v);
                    for i in 0..N {
                        result[i] = T::conditionally_select(cs, &condition, &vals[i], &result[i])?
                    }
                }
                Ok(result)
            }
        }
    }

    pub fn map<CS: ConstraintSystem<E>, T: Vecable<E>, F: Fn (usize) -> T>(
        &self,
        cs: &mut CS,
        f: F
    ) -> Result<T, SynthesisError> {
        let [result] = self.map_multiple(cs, |i| [f(i)])?;
        Ok(result)
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        let num = Num::conditionally_select(cs, condition, &a.num, &b.num)?;
        let bounds = a.bounds.union(b.bounds);
        Ok(Self{ num,  bounds })
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.num, &b.num)
    }

    pub fn is_less_or_equal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        bound: usize
    ) -> Result<Boolean, SynthesisError> {
        assert!(bound >= self.lower() && bound <= self.upper());
        let bound_num = Num::Constant(u64_to_ff(bound as u64));
        let diff = bound_num.sub(cs, &self.num)?;

        // compute the witness for diff and -diff, whichever
        // one of them is < bound.upper (< 2**64)
        let pval = diff.get_value().map(|mut v| {
            let repr: <E::Fr as PrimeField>::Repr = v.into_repr();
            v = v.clone();
            if !repr.as_ref()[1..].iter().all(|l| *l == 0) {
                v.negate();
            }
            v
        });
        let pos = Num::alloc(cs, pval)?;
        let neg = pos.negate(cs)?;

        // enforce pos is the "small" value
        constrain_bit_length(cs, &pos, byte_length(self.upper()) * 8)?;

        // enforce that one of them is equal to diff
        let poseq = Num::equals(cs, &pos, &diff)?;
        let negeq = Num::equals(cs, &neg, &diff)?;
        let oneeq = Boolean::or(cs, &poseq, &negeq)?;
        Boolean::enforce_equal(cs, &oneeq, &Boolean::constant(true))?;

        // return true iff pos == diff
        Ok(poseq)
    }
}

pub type Length<E> = BoundedU64<E>;