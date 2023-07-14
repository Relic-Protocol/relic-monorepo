use std::marker::PhantomData;
use std::ops::Deref;

use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::bellman::Field;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;
use franklin_crypto::bellman::pairing::ff::PrimeField;

use super::num::*;
use super::bounded::*;

pub trait Selectable<E: Engine>: Sized {
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError>;
}

pub trait Vecable<E: Engine>: Selectable<E> + Sized + Clone {
    type Raw: Default + Clone;
    fn get_value(&self) -> Option<Self::Raw>;
    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Self::Raw>) -> Result<Self, SynthesisError>;
    fn constant(value: Self::Raw) -> Self;
    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError>;
    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<(), SynthesisError>;
    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError>;
    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

impl<E: Engine> Selectable<E> for Byte<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Byte::<E>::conditionally_select(cs, flag, a, b)
    }
}

impl<E: Engine> Vecable<E> for Byte<E> {
    type Raw = u8;

    fn get_value(&self) -> Option<Self::Raw> {
        self.get_byte_value()
    }

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Self::Raw>) -> Result<Self, SynthesisError> {
        let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
        Byte::from_num(cs, num)
    }

    fn constant(value: Self::Raw) -> Self {
        Byte::constant(value)
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

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.into_num().inputize(cs)
    }
}

impl<E: Engine> Selectable<E> for Num<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Num::<E>::conditionally_select(cs, flag, a, b)
    }
}

impl<E: Engine> Vecable<E> for Num<E> {
    type Raw = E::Fr;

    fn get_value(&self) -> Option<Self::Raw> {
        self.get_value()
    }

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Self::Raw>) -> Result<Self, SynthesisError> {
        Num::alloc(cs, value.map(|v| v))
    }

    fn constant(value: Self::Raw) -> Self {
        Num::Constant(value)
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

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.get_variable().inputize(cs)
    }
}

impl<E: Engine> Selectable<E> for Nibble<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(cs: &mut CS, flag: &Boolean, a: &Self, b: &Self) -> Result<Self, SynthesisError> {
        Nibble::conditionally_select(cs, flag, a, b)
    }
}

impl<E: Engine> Vecable<E> for Nibble<E> {
    type Raw = u8;

    fn get_value(&self) -> Option<Self::Raw> {
        self.to_byte().get_byte_value()
    }

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Self::Raw>) -> Result<Self, SynthesisError> {
        Nibble::alloc(cs, value.map(|v| v))
    }

    fn constant(value: Self::Raw) -> Self {
        Nibble::constant(value)
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        self.to_byte().enforce_equal(cs, &other.to_byte())
    }

    fn conditionally_enforce_equal<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError> {
        Byte::conditionally_enforce_equal(cs, flag, &a.to_byte(), &b.to_byte())
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Nibble::equals(cs, a, b)
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.to_byte().into_num().get_variable().inputize(cs)
    }
}

#[derive(Clone)]
pub struct VarVec<E: Engine, T: Vecable<E>> {
    // vector of all values
    vals: Vec<T>,
    // length variable along with bounds, upper bound should be vals.len()
    length: BoundedU64<E>
}

impl<E: Engine, T: Vecable<E>> VarVec<E, T> {
    pub fn alloc_with_bounds<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bounds: Bounds,
        values: Option<&[T::Raw]>
    ) -> Result<Self, SynthesisError> {
        let len = values.map(|vals| vals.len());
        let default = &T::Raw::default();
        let mut vals = Vec::with_capacity(bounds.upper);
        for i in 0..bounds.upper {
            vals.push(T::alloc(cs, values.map(|vals| vals.get(i).map(Clone::clone).unwrap_or(default.clone())))?);
        }

        let length = BoundedU64::alloc(cs, bounds, len)?;
        Ok(Self { vals, length })
    }

    pub fn from(values: &[T]) -> Self {
        let length = BoundedU64::constant(values.len());
        let vals = values.into_iter().map(Clone::clone).collect::<Vec<_>>();

        Self { vals, length }
    }

    pub fn get_value(&self) -> Option<Vec<T::Raw>> {
        self.length.get_value().map(|len| {
            self.vals[..len].iter().map(|v| v.get_value().unwrap()).collect::<Vec<_>>()
        })
    }

    // allocates a new VarVec with unconstrained values, but assignments matching the given slice bounds
    pub fn witness_slice<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        start: BoundedU64<E>,
        end: BoundedU64<E>
    ) -> Result<VarVec<E, T>, SynthesisError> {
        let default = &T::Raw::default();
        let length = end.sub(cs, &start)?;
        let mut vals = Vec::with_capacity(length.upper());

        // convert bounds assigned values to usizes
        let bounds = start.get_value().zip(end.get_value());

        // allocate and unconstrained value for each index, assign based on self.vals
        for i in 0..length.upper() {
            vals.push(T::alloc(cs, bounds.map(|(start, end)| {
                assert!(end >= start);
                assert!(end <= self.vals.len());
                assert!(end - start <= self.vals.len());
                if i < end - start {
                    self.vals[start+i].get_value().unwrap()
                } else {
                    default.clone()
                }
            }))?);
        }

        Ok(Self { vals, length })
    }

    // returns two new VarVecs with unconstrained values, but assignments matching the original VarVec
    pub fn witness_split<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        idx: BoundedU64<E>
    ) -> Result<(VarVec<E, T>, VarVec<E, T>), SynthesisError> {
        Ok((
            self.witness_slice(cs, BoundedU64::constant(0), idx)?,
            self.witness_slice(cs, idx, self.length)?
        ))
    }

    pub fn suffix<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        idx: usize
    ) -> Result<VarVec<E, T>, SynthesisError> {
        let vals = self.vals.iter().skip(idx).map(Clone::clone).collect();
        let length = self.length.sub_const(cs, idx)?;
        Ok(Self{ vals, length })
    }

    pub fn resize(
        &self,
        length: BoundedU64<E>
    ) -> Self {
        assert!(length.upper() <= self.length.upper());
        let vals = self.vals.iter().take(length.upper()).map(Clone::clone).collect();
        Self { vals: vals, length }
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        assert!(a.vals.len() == b.vals.len());
        let mut equal = BoundedU64::equals(cs, &a.length(), &b.length())?;
        let length = a.length();
        let mut reached_end = Boolean::Constant(false);
        for i in 0..a.vals.len() {
            let idx = BoundedU64::constant(i);
            let end = BoundedU64::equals(cs, &idx, &length)?;
            reached_end = Boolean::or(cs, &reached_end, &end)?;

            let val_eq = T::equals(cs, &a.vals[i], &b.vals[i])?;
            let i_result = Boolean::or(cs, &val_eq, &reached_end)?;
            equal = Boolean::and(cs, &equal, &i_result)?;
        }
        Ok(equal)
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.length.get_variable().inputize(cs)?;
        for i in 0..self.vals.len() {
            self.vals[i].inputize(cs)?;
        }
        Ok(())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        // sort a and b by max length
        let (a, b, flag) = if a.length.upper() < b.length.upper() { (a, b, *flag) } else { (b, a, flag.not()) };
        let length = BoundedU64::conditionally_select(cs, &flag, &a.length, &b.length)?;
        let max = length.upper();
        let mut vals: Vec<T> = std::iter::repeat(T::constant(T::Raw::default())).take(max).collect();
        for i in 0..max {
            if i < a.length.upper() {
                vals[i] = <T as Selectable<E>>::conditionally_select(cs, &flag, &a.vals[i], &b.vals[i])?;
            } else {
                // optimization: we know |a.length| <= i, so if we're selecting |a|
                // then these vals are unused; hence we can just use the |b| vals
                vals[i] = b.vals[i].clone();
            }
        }
        Ok(Self { vals, length })
    }

    pub fn prepend<CS: ConstraintSystem<E>>(&self, cs: &mut CS, prefix: &[T]) -> Result<Self, SynthesisError> {
        let length = self.length.add_const(cs, prefix.len())?;
        let vals: Vec<T> = prefix.iter().chain(self.vals.iter()).map(|e| e.clone()).collect();
        Ok(Self { vals, length })
    }

    pub fn constant(value: Vec<T::Raw>) -> Self {
        let length = BoundedU64::constant(value.len());
        let vals = value.iter().map(|v| T::constant(v.clone())).collect();
        Self { length, vals }
    }

    pub fn length(&self) -> BoundedU64<E> { self.length }
    pub fn vals(&self) -> &[T] { self.vals.as_slice() }
}

// Wrapper type with const generic type bounds for convenience
// The bounds are only not strictly guaranteed at compile-time
// Bounds are checked via assert!()s at run-time
#[derive(Clone)]
pub struct VarVecMN<E: Engine, T: Vecable<E>, const N: usize, const M: usize>(VarVec<E, T>, PhantomData<([usize; N], [usize; M])>);
pub type VarVecN<E, T, const N: usize> = VarVecMN<E, T, 0, N>;

impl<E: Engine, T: Vecable<E>, const M: usize, const N: usize> VarVecMN<E, T, M, N> {
    fn check_bounds(vec: &VarVec<E, T>) {
        // runtime checks that the type bounds are valid
        assert!(M <= N);
        assert!(vec.length().bounds().includes(Bounds::new(M, N)));
    }
}

impl<E: Engine, T: Vecable<E>, const M: usize, const N: usize> Deref for VarVecMN<E, T, M, N> {
    type Target = VarVec<E, T>;

    // allow dereference to VarVec
    fn deref(&self) -> &Self::Target {
        Self::check_bounds(&self.0);
        &self.0
    }
}


impl<E: Engine, T:Vecable<E>, const M: usize, const N: usize> VarVecMN<E, T, M, N> {
    pub fn from(vv: VarVec<E, T>) -> Self {
        Self::check_bounds(&vv);
        Self(vv, PhantomData)
    }
}

impl<E: Engine, T: Vecable<E>, const M: usize, const N: usize> Selectable<E> for VarVecMN<E, T, M, N> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        Self::check_bounds(&a);
        Self::check_bounds(&b);
        Ok(Self(VarVec::conditionally_select(cs, flag, &a, &b)?, PhantomData))
    }
}

impl<E: Engine, T: Vecable<E>, const M: usize, const N: usize> Vecable<E> for VarVecMN<E, T, M, N> {
    type Raw = Vec<T::Raw>;

    fn get_value(&self) -> Option<Self::Raw> {
        Self::check_bounds(&self);
        self.vals.iter().map(|v| v.get_value()).collect::<Option<_>>()
    }

    fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Self::Raw>) -> Result<Self, SynthesisError> {
        assert!(M <= N);
        Ok(Self(VarVec::alloc_with_bounds(cs, Bounds::new(M, N), value.as_ref().map(Vec::as_slice))?, PhantomData))
    }

    fn constant(value: Self::Raw) -> Self {
        assert!(value.len() >= M && value.len() <= N);
        Self ( VarVec::constant(value), PhantomData)
    }

    fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        Self::check_bounds(&self);
        Self::check_bounds(&other);
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
        Self::check_bounds(a);
        Self::check_bounds(b);
        for (av, bv) in a.vals.iter().zip(b.vals.iter()) {
            T::conditionally_enforce_equal(cs, flag, av, bv)?;
        }
        Ok(())
    }

    fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        Self::check_bounds(a);
        Self::check_bounds(b);
        VarVec::equals(cs, &a, &b)
    }

    fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        Self::check_bounds(&self);
        VarVec::inputize(&self, cs)
    }
}

impl<E: Engine, T: Vecable<E>, const N: usize> From<[T; N]> for VarVecN<E, T, N> {
    fn from(vals: [T; N]) -> Self {
        let length = BoundedU64::constant(N);
        let vals = Vec::from(vals);
        Self(VarVec { length, vals }, PhantomData)
    }
}

pub trait Numable<E: Engine>: Sized {
    const NUM_BITS: u32;
    fn to_num(&self) -> Num<E>;
    fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError>;
}

impl<E: Engine> Numable<E> for Num<E> {
    const NUM_BITS: u32 = E::Fr::CAPACITY;

    fn to_num(&self) -> Num<E> {
        *self
    }

    fn from_num<CS: ConstraintSystem<E>>(_cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError> {
        Ok(num)
    }
}

impl<E: Engine> Numable<E> for Byte<E> {
    const NUM_BITS: u32 = 8;

    fn to_num(&self) -> Num<E> {
        self.inner
    }

    fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError> {
        Byte::from_num(cs, num)
    }
}

impl<E: Engine> Numable<E> for Nibble<E> {
    const NUM_BITS: u32 = 4;

    fn to_num(&self) -> Num<E> {
        self.to_byte().inner
    }

    fn from_num<CS: ConstraintSystem<E>>(cs: &mut CS, num: Num<E>) -> Result<Self, SynthesisError> {
        Nibble::from_num(cs, num)
    }
}

impl<E: Engine, T: Vecable<E> + Numable<E>> VarVec<E, T> {
    pub fn weighted_sum<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        base: E::Fr
    ) -> Result<Num<E>, SynthesisError> {
        let mut values = Vec::with_capacity(self.length.upper());
        let mut acc = Num::zero();
        values.push(acc);
        for i in 0..self.length.upper() {
            // compute acc = acc * base + vals[i] in one gate
            acc = Num::fma_with_coefficients(
                cs,
                &acc,
                &Num::Constant(base),
                &self.vals[i].to_num(),
                E::Fr::one(),
                E::Fr::one()
            )?;
            values.push(acc);
        }

        self.length.map(cs, |i| values[i])
    }
}

impl<E: Engine> VarVec<E, Byte<E>> {
    pub fn to_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        Self::weighted_sum(&self, cs, u64_to_ff(256))
    }
}