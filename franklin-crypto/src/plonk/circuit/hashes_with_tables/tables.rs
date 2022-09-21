use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;

use super::utils::*;
use itertools::Itertools;
use std::sync::Arc;


pub fn add_table_once<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, table: LookupTableApplication<E>
) -> Result<Arc<LookupTableApplication<E>>, SynthesisError>
{
    let existing_table_or_err = cs.get_table(&table.functional_name());
    if existing_table_or_err.is_ok() {
        existing_table_or_err
    }
    else {
        cs.add_table(table)
    }
}


// GENERAL PURPOSE TABLES (so to say)
// ----------------------------------------------------------------------------------------------------------------------------


// for given bit_width, rotation parameter, extraction parameter and base construct the following table:
// first column containts all values of x in the range [0, 2^bits - 1]
// the corresponding value in the second column is sparse representation of x (with extraction) 
// while the value in the thrid column is sparse representation of shifted and extracted value of x 
// (if shift = 0) then the third column is simpy zero
// see utils file for more details
#[derive(Clone)]
pub struct SparseRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    bits: usize,
    rotation: usize,
    extraction: usize,
    base: u64,
    name: &'static str,
}

impl<E: Engine> SparseRotateTable<E> {

    pub fn new(bits: usize, rotation: usize, extraction: usize, base: u64, name: &'static str) -> Self {
        let mut key = Vec::with_capacity(1 << bits);
        let mut value_0 = Vec::with_capacity(1 << bits);
        let mut value_1 = Vec::with_capacity(1 << bits);
        let mut map = std::collections::HashMap::with_capacity(1 << bits);

        let flag = rotation == 0;
        let zero = E::Fr::zero();

        for x in 0..(1 << bits) {
            let y = if extraction > 0 {
                map_into_sparse_form(rotate_extract(x, 0, extraction), base as usize)
            }
            else {
                map_into_sparse_form(x, base as usize)
            };
            let z = map_into_sparse_form(rotate_extract(x, rotation, extraction), base as usize);

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            let z = if flag { zero.clone() } else { E::Fr::from_str(&z.to_string()).unwrap() };

            key.push(x);
            value_0.push(y);
            value_1.push(z);

            map.insert(x, (y, z));
        }

        Self {
            table_entries: [key, value_0, value_1],
            table_lookup_map: map,
            bits,
            rotation,
            extraction,
            base,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for SparseRotateTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SparseRotateTable")
            .field("bits", &self.bits)
            .field("rotation", &self.rotation)
            .field("extraction", &self.extraction)
            .field("base", &self.base)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for SparseRotateTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << self.bits
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        (column_num == 2) && (self.rotation == 0)
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// Sha256 normalization table is parametrized by the following parameters: 
// sparse representation INPUT base inp_base, num of input chunks, two OUTPUT bases out_base0, out_base1,
// and corresponding transformation functions:
// f0: [0, inp_base) -> [0, out_base0); f1: [0, inp_base) -> [0, out_base1).
// let x be any number in [0, inp_base^num_chunks - 1], hence x can ne represented as inp_base-ary number with num_of_chunks digits:
// x = \sum_{i=0}^{num_chunks-1} x_i * inp_base^i, where each x_i \in [0, inp_base-1]
// the purpose of normalization table is to transform every such x into pair (y0, y1):
// yk = \sum_{i=0}^{num_chunks-1} fk(x_i) out_basek^i, and k = {0, 1}
// the table has the following columns: (x, y0, y1)
// NB: in practice the transform for the third column would be simple xor
#[derive(Clone)]
pub struct MultiBaseNormalizationTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    num_chunks: usize,
    input_base: u64,
    first_output_base: u64,
    second_output_base: u64,
    name: &'static str,
}

impl<E: Engine> MultiBaseNormalizationTable<E> {
    pub fn new<F0, F1>(num_chunks: usize, inp_base: u64, out_base0: u64, out_base1: u64, f0: F0, f1: F1, name: &'static str) -> Self 
    where F0 : Fn(u64) -> u64, F1 : Fn(u64) -> u64
    {
        let table_size = pow(inp_base as usize, num_chunks);
        let mut keys_vec = Vec::with_capacity(table_size);
        let mut values0_vec = Vec::with_capacity(table_size);
        let mut values1_vec = Vec::with_capacity(table_size);
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let input_base_fr = u64_to_ff::<E::Fr>(inp_base);
        let first_output_base_fr = u64_to_ff::<E::Fr>(out_base0);
        let second_output_base_fr = u64_to_ff::<E::Fr>(out_base1);
        let zero_fr = E::Fr::zero();

        for coefs in (0..num_chunks).map(|_| 0..inp_base).multi_cartesian_product() {
            let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&input_base_fr);
                tmp.add_assign(&u64_to_ff(*x));
                tmp
            });

            let value0 = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&first_output_base_fr);
                tmp.add_assign(&u64_to_ff(f0(*x)));
                tmp
            });

            let value1 = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&second_output_base_fr);
                tmp.add_assign(&u64_to_ff(f1(*x)));
                tmp
            });

            keys_vec.push(key);
            values0_vec.push(value0);
            values1_vec.push(value1);
            map.insert(key, (value0, value1));
        }

        Self {
            table_entries: [keys_vec, values0_vec, values1_vec],
            table_lookup_map: map,
            num_chunks : num_chunks,
            input_base: inp_base,
            first_output_base : out_base0,
            second_output_base : out_base1,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for MultiBaseNormalizationTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MultiBaseNormalizationTable")
            .field("num_chunks", &self.num_chunks)
            .field("input_base", &self.input_base)
            .field("first_output_base", &self.first_output_base)
            .field("second_output_base", &self.second_output_base)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for MultiBaseNormalizationTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        pow(self.input_base as usize, self.num_chunks)
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// for columns (a, b, c) this table asserts that c = (a ^ b) >>> shift (cyclic shift of 32 bit values)
// if shift is zero, than it is simple xor table: c = a ^ b;
#[derive(Clone)]
pub struct XorRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    shift: u32,
    name: &'static str,
}


impl<E: Engine> XorRotateTable<E> {
    pub fn new(bits: usize, shift: u32, name: &'static str) -> Self {
        let mut keys1 = Vec::with_capacity(1 << bits);
        let mut keys2 = Vec::with_capacity(1 << bits);
        let mut values = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let tmp: u32 = x ^ y;
                let z : u32 = if shift > 0 {
                    tmp.rotate_right(shift)
                }
                else {
                    tmp
                };

                let x = u64_to_ff(x as u64);
                let y = u64_to_ff(y as u64);
                let z = u64_to_ff(z as u64);

                keys1.push(x);
                keys2.push(y);
                values.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [keys1, keys2, values],
            table_lookup_map: map,
            bits,
            shift,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for XorRotateTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("XorRotateTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for XorRotateTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
    }
    fn num_keys(&self) -> usize {
        2
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// The following tables check booleanity of three elemets at once:
// it contains all possible triples [a0, a1, a2] where each a_i \in {0, 1}
#[derive(Clone)]
pub struct BooleanityTable<E: Engine> {
    table_entries: Vec<[E::Fr; 3]>,
    name: &'static str,
}


impl<E: Engine> BooleanityTable<E> {
    pub fn new(name: &'static str) -> Self {
        let entries = vec![
            [E::Fr::zero(), E::Fr::zero(), E::Fr::zero()],
            [E::Fr::zero(), E::Fr::zero(), E::Fr::one()],
            [E::Fr::zero(), E::Fr::one(), E::Fr::zero()],
            [E::Fr::zero(), E::Fr::one(), E::Fr::one()],
            [E::Fr::one(), E::Fr::zero(), E::Fr::zero()],
            [E::Fr::one(), E::Fr::zero(), E::Fr::one()],
            [E::Fr::one(), E::Fr::one(), E::Fr::zero()],
            [E::Fr::one(), E::Fr::one(), E::Fr::one()],
        ];

        Self {
            table_entries: entries,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for BooleanityTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BooleanityTable").finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for BooleanityTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << 3
    }
    fn num_keys(&self) -> usize {
        3
    }
    fn num_values(&self) -> usize {
        0
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        let mut result  = vec![vec![]; 3];
        for [e0, e1, e2] in self.table_entries.iter() {
            result[0].push(*e0);
            result[1].push(*e1);
            result[2].push(*e2);
        }

        result
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, _column_num: usize) -> bool {
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        let check_booleanity = |fr: &E::Fr| -> bool { (*fr == E::Fr::zero()) || (*fr == E::Fr::one()) };
        values.iter().all(|x| check_booleanity(x))
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        for set in self.table_entries.iter() {
            if &set[..] == keys {
                return Ok(vec![])
            }
        }

        panic!("Invalid input into table {}: {:?}", self.name(), keys);
        // Err(SynthesisError::Unsatisfiable)
    }
}

