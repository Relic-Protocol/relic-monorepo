use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;

use franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;
use franklin_crypto::plonk::circuit::sha256::sha256 as sha256_no_tables;

use sha2::{Sha256, Digest as Sha256Digest};

use super::{Digest, RawDigest, NumExtension};

pub const MERKLE_DIGEST_NUM_BYTES: usize = 32;
pub const MERKLE_DIGEST_NUM_WORDS: usize = 4;

#[derive(Debug)]
pub struct MerkleGadget<E: Engine> {
    table_gadget: Option<Sha256Gadget<E>>,
}

fn bytes_to_bools<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Vec<Boolean> {
    bytes.iter().flat_map(|byte| {
        let mut bits = byte.into_num().into_bits_le(cs, Some(8)).unwrap();
        bits.reverse();
        bits
    }).collect()
}

fn bools_to_bytes<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, bools: &[Boolean]) -> Result<Vec<Byte<E>>, SynthesisError> {
    let two = E::Fr::from_str("2").unwrap();
    let nums: Vec<_> = bools.iter().map(|b| Ok::<_, SynthesisError>(Num::alloc(cs, b.get_value_in_field::<E>())?)).collect::<Result<_,_>>()?;
    nums.chunks(8).map(
        |chunk| {
            let num = Num::weighted_sum(cs, chunk, &two)?;
            Byte::from_num(cs, num)
        }
    ).collect()
}

pub type RawMerkleDigest<E> = RawDigest<E, MERKLE_DIGEST_NUM_WORDS>;
pub type MerkleDigest<E> = Digest<E, MERKLE_DIGEST_NUM_WORDS>;

impl<E: Engine> MerkleGadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS, use_tables: bool) -> Result<Self, SynthesisError> {
        let table_gadget = if use_tables { Some(Sha256Gadget::new(cs, None, None, false, false, 0, "")?) } else { None };
        Ok(Self { table_gadget })
    }

    fn hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &[Byte<E>]) -> Result<[Byte<E>; MERKLE_DIGEST_NUM_BYTES], SynthesisError> {
        let out = match &self.table_gadget {
            Some(gadget) => gadget.sha256_from_bytes_to_bytes(cs, &input)?.to_vec(),
            None => {
                let inp_bools = bytes_to_bools(cs, input);
                let out_bools = sha256_no_tables(cs, &inp_bools)?;
                bools_to_bytes(cs, &out_bools)?
            }
        };
        Ok(out.as_slice().try_into().expect("unexpected digest size"))
    }

    pub fn merkle_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS, inputs: Vec<Vec<Byte<E>>>) -> Result<MerkleDigest<E>, SynthesisError> {
        let mut values = inputs;
        assert!(values.len() > 0);
        while values.len() != 1 {
            assert!(values.len() % 2 == 0);
            values = values.chunks(2).map(
                |chunk| {
                    let inp = [chunk[0].as_slice(), chunk[1].as_slice()].concat();
                    self.hash(cs, &inp).map(|h| h.to_vec())
                }
            ).collect::<Result<Vec<_>, _>>()?;
        }
        MerkleDigest::from_le_bytes(cs, &values[0])
    }

    pub fn verify<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        root: MerkleDigest<E>,
        index: Num<E>,
        value: &[Byte<E>],
        proof: &[Vec<Byte<E>>],
    ) -> Result<(), SynthesisError> {
        let mut current = value;
        let bits = index.into_bits_le(cs, Some(proof.len()))?;
        let mut buf;
        for (bit, witness) in bits.iter().zip(proof.iter()) {
            let len = current.len() + witness.len();
            let input_if_0 = [current, witness].concat();
            let input_if_1 = [witness, current].concat();
            let input = (0..len).map(
                |i| Byte::conditionally_select(cs, &bit, &input_if_1[i], &input_if_0[i])
            ).collect::<Result<Vec<_>, _>>()?;
            buf = self.hash(cs, &input)?;
            current = &buf;
        }
        let computed_root = MerkleDigest::from_le_bytes(cs, &current)?;
        computed_root.enforce_equal(cs, &root)
    }

    pub fn raw_merkle_root(inputs: Vec<Vec<u8>>) -> RawMerkleDigest<E> {
        let mut values = inputs;
        while values.len() != 1 {
            assert!(values.len() % 2 == 0);
            values = values.chunks(2).map(
                |chunk| { 
                    let mut hasher = Sha256::new();
                    hasher.update(&chunk[0]);
                    hasher.update(&chunk[1]);
                    hasher.finalize().to_vec()
                }
            ).collect();
        }
        RawMerkleDigest::from_bytes32(values[0].clone().try_into().expect("unexpected digest size"))
    }
}
