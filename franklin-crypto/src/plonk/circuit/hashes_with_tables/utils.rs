use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{ Zero, One, PrimInt };
use std::{ iter, mem };


// for given x=(x_0, x_1, ..., x_n) extract the k lower bits: y = (x_0, x_1, ..., x_{k-1}, 0, ..., 0)
// and then rotate
// NOTE: by rotate we always mean right rotate of 32-bit numbers!
pub fn rotate_extract(value: usize, rotation: usize, extraction: usize) -> usize
{
    let temp = if extraction > 0 {value & ((1 << extraction) - 1)} else {value}; 
    let res = if rotation > 0 {(temp >> rotation) + ((temp << (32 - rotation)) & 0xffffffff) } else {temp};

    res
}

pub fn shift_right(value: usize, shift: usize) -> usize
{
    if shift > 0 {value >> shift} else {value}
}


pub fn pow(base: usize, exp: usize) -> usize {

    let mut res = 1;
    for _i in 0..exp {
        res *= base;
    }

    res
}

pub fn biguint_pow(base: usize, exp: usize) -> BigUint {
    let mut res = BigUint::one();
    for _i in 0..exp {
        res *= base;
    }

    res
}

pub fn u64_to_ff<Fr: PrimeField>(n: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let res = Fr::from_repr(repr).expect("should parse");
    res
}

pub fn u64_exp_to_ff<Fr: PrimeField>(n: u64, exp: u64) -> Fr {
    if exp == 0 {
        return Fr::one();
    }

    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let res = Fr::from_repr(repr).expect("should parse");
    res.pow(&[exp])
}

pub fn ff_to_u64<Fr: PrimeField>(fr: &Fr) -> u64 {
    let repr = fr.into_repr();
    for i in 1..4 {
        assert_eq!(repr.as_ref()[i], 0);
    }
    repr.as_ref()[0]
}

fn biguint_to_ff<Fr: PrimeField>(value: &BigUint) -> Fr {
    Fr::from_str(&value.to_str_radix(10)).unwrap()
}


// converts x = (x_0, x_1, ..., x_n) - bit decomposition of x into y = \sum_{i=1}^{n} x_i * base^i
pub fn map_into_sparse_form(input: usize, base: usize) -> BigUint
{
    // if base is zero, than no convertion is actually needed
    if base == 0 {
        return BigUint::from(input);
    }
    
    let mut out = BigUint::zero();
    let mut base_accumulator = BigUint::one();
    let mut converted = input;

    while converted > 0 {
        let sparse_bit = converted & 1;
        converted >>= 1;
        if sparse_bit > 0 {
            out += base_accumulator.clone();
        }
        base_accumulator *= base;
    }
    
    out
}

pub fn map_from_sparse_form(input: usize, base: usize) -> usize
{
    let mut target : usize = input;
    let mut output : usize = 0;
    let mut count : usize = 0;

    while target > 0 {
        let slice = target % base;
        // althoough slice is not bound to {0, 1} we are only interested in its value modulo 2
        let bit = slice & 1usize;
        output += bit << count;
        count += 1;
        target = target / base;
    }

    output
}


// in general all bit-friendly transformations (such as xor or SHA256 majority and choose operations)
// are hadled by the gadget library itself with the use of tables
// however, in some our wires are actually constants and not allocated variables
// for them we do not want apply the common strategy 
// ( split in chunks -- chunk-by-chunk transform via tables -- compose chunks back )
// but want to do all the bitwise transformations on the whole constant number in one turn
// this is done by the corresponding "normalizer" mappings, contained in this module
pub fn general_normalizer<Fr: PrimeField>(fr : Fr, bit_table: &[u64], base: u64) -> Fr
{
    let mut input = BigUint::default();
    let fr_repr = fr.into_repr();
    for n in fr_repr.as_ref().iter().rev() {
        input <<= 64;
        input += *n;
    }

    let mut acc : u64 = 0; 
    let mut count = 0;
 
    while !input.is_zero() {
        let remainder = (input.clone() % BigUint::from(base)).to_u64().unwrap();
        let bit = bit_table[remainder as usize];
        acc += bit << count;
        input /= base;
        count += 1;
    }

    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = acc;
    let res = Fr::from_repr(repr).expect("should parse");

    res
}

/// Normalizes an input value by taking `digits` in the `input_base`,
/// then transforming this "digits" with transformation function,
/// and finally treating transformation results as digits into `output_base` 
pub fn func_normalizer<Fr: PrimeField, T: Fn(u64) -> u64>(fr : Fr, input_base: u64, output_base: u64, transform_f: T) -> Fr
{
    let mut input = BigUint::default();
    let fr_repr = fr.into_repr();
    for n in fr_repr.as_ref().iter().rev() {
        input <<= 64;
        input += *n;
    }

    let mut acc = BigUint::default(); 
    let mut base = BigUint::one();
 
    while !input.is_zero() {
        let remainder = (input.clone() % BigUint::from(input_base)).to_u64().unwrap();
        let output_chunk = transform_f(remainder);
        acc += output_chunk * base.clone();
        input /= input_base;
        base *= output_base;
    }

    let res = Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
    res
}


// returns closets upper integer to a / b
pub fn round_up(a: usize, b : usize) -> usize {
    let additional_chunks : usize = if a % b > 0 {1} else {0};
    a/b + additional_chunks
}


pub fn num_bits<T: PrimInt>(x: T) -> usize {
    const BITS_PER_BYTE: usize = 8;
    BITS_PER_BYTE * std::mem::size_of::<T>() - (x.leading_zeros() as usize)
}


pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I where I: Iterator {
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>) where I: Iterator;

impl<I> Iterator for Iter<I> where I: Iterator {
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}
