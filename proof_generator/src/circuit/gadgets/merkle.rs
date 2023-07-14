use std::marker::PhantomData;

use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;

use super::utils::digest::{RawDigest, Digest};

pub trait MerkleCompressor<E: Engine, const N: usize, const M: usize> {
    type Params: Clone;
    fn compress<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: Digest<E, N, M>, y: Digest<E, N, M>) -> Result<Digest<E, N, M>, SynthesisError>;
    fn compress_raw(x: RawDigest<E, N, M>, y: RawDigest<E, N, M>, params: Self::Params) -> RawDigest<E, N, M>;
}

pub struct MerkleGadget<'a, E: Engine, const N: usize, const M: usize, C: MerkleCompressor<E, N, M>> {
    compressor: &'a C,
    phantom: PhantomData<E>
}

impl<'a, E: Engine, const N: usize, const M: usize, C: MerkleCompressor<E, N, M> + 'a> MerkleGadget<'a, E, N, M, C> {
    pub fn new(compressor: &'a C) -> Self {
        Self { compressor, phantom: PhantomData }
    }

    fn merklize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        inputs: Vec<Digest<E, N, M>>
    ) -> Result<(Digest<E, N, M>, Vec<Vec<Digest<E, N, M>>>), SynthesisError>
    {
        let mut intermediate = Vec::new();
        let mut values = inputs;
        assert!(values.len() > 0);
        while values.len() != 1 {
            assert!(values.len() % 2 == 0);
            let layer = values;
            values = layer.chunks(2).map(
                |chunk| {
                    self.compressor.compress(cs, chunk[0].clone(), chunk[1].clone())
                }
            ).collect::<Result<Vec<_>, _>>()?;
            intermediate.push(layer);
        }
        let root = values.pop().unwrap();
        Ok((root, intermediate))
    }

    fn raw_merklize(inputs: Vec<RawDigest<E, N, M>>, params: C::Params) -> (RawDigest<E, N, M>, Vec<Vec<RawDigest<E, N, M>>>) {
        let mut intermediate = Vec::new();
        let mut values = inputs;
        assert!(values.len() > 0);
        while values.len() != 1 {
            assert!(values.len() % 2 == 0);
            let layer = values;
            values = layer.chunks(2).map(
                |chunk| { 
                    C::compress_raw(chunk[0], chunk[1], params.clone())
                }
            ).collect();
            intermediate.push(layer);
        }
        let root = values.pop().unwrap();
        (root, intermediate)
    }

    pub fn merkle_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS, inputs: Vec<Digest<E, N, M>>) -> Result<Digest<E, N, M>, SynthesisError>
    {
        let (root, _) = self.merklize(cs, inputs)?;
        Ok(root)
    }

    pub fn raw_merkle_root(inputs: Vec<RawDigest<E, N, M>>, params: C::Params) -> RawDigest<E, N, M> {
        let (root, _) = Self::raw_merklize(inputs, params);
        root
    }

    pub fn raw_compute_proof(
        index: usize,
        inputs: Vec<RawDigest<E, N, M>>,
        params: C::Params
    ) -> Vec<RawDigest<E, N, M>> {
        assert!(index < inputs.len());
        let mut result = Vec::new();
        let (_, intermediate) = Self::raw_merklize(inputs, params);
        let mut idx = index;
        for layer in intermediate {
            let proof_node = layer[idx ^ 1];
            idx >>= 1;
            result.push(proof_node);
        }
        result
    }

    pub fn recompute_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        index: Num<E>,
        value: Digest<E, N, M>,
        proof: &[Digest<E, N, M>],
    ) -> Result<Digest<E, N, M>, SynthesisError> {
        let mut current = value;
        let bits = index.into_bits_le(cs, Some(proof.len()))?;
        for (bit, witness) in bits.iter().zip(proof.iter()) {
            let left = Digest::conditionally_select(cs, bit, witness, &current)?;
            let right = Digest::conditionally_select(cs, bit, &current, witness)?;
            current = self.compressor.compress(cs, left, right)?;
        }
        Ok(current)
    }

    pub fn verify<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        index: Num<E>,
        value: Digest<E, N, M>,
        proof: &[Digest<E, N, M>],
        root: Digest<E, N, M>,
    ) -> Result<(), SynthesisError> {
        let computed = self.recompute_root(cs, index, value, proof)?;
        computed.enforce_equal(cs, &root)
    }
}