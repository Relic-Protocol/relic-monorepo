use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::Engine;
use franklin_crypto::bellman::PrimeField;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;
use franklin_crypto::plonk::circuit::sha256::sha256 as sha256_no_tables;
use sha2::{Digest as Sha256LibDigest, Sha256};

use super::utils::digest::{Digest, RawDigest, Hasher};
use super::merkle::{MerkleGadget, MerkleCompressor};
use super::utils::num::NumExtension;

const SHA256_DIGEST_NUM_WORDS: usize = 4;
const SHA256_DIGEST_WORD_SIZE: usize = 8;
pub type RawSha256Digest<E> = RawDigest<E, SHA256_DIGEST_NUM_WORDS, SHA256_DIGEST_WORD_SIZE>;
pub type Sha256Digest<E> = Digest<E, SHA256_DIGEST_NUM_WORDS, SHA256_DIGEST_WORD_SIZE>;

fn bytes_to_bools<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, bytes: &[Byte<E>]) -> Vec<Boolean> {
    bytes.iter().flat_map(|byte| {
        let mut bits = byte.into_num().into_bits_le(cs, Some(8)).unwrap();
        bits.reverse();
        bits
    }).collect()
}

fn bools_to_bytes<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, bools: &[Boolean]) -> Result<Vec<Byte<E>>, SynthesisError> {
    let two = E::Fr::from_str("2").unwrap();
    let nums: Vec<Num<E>> = bools.iter().map(|b| Num::from_boolean_is(*b)).collect();
    nums.chunks(8).map(
        |chunk| {
            let num = Num::weighted_sum(cs, chunk, &two)?;
            Byte::from_num(cs, num)
        }
    ).collect()
}

#[derive(Debug)]
pub struct Sha256Hasher<E: Engine> {
    table_gadget: Option<Sha256Gadget<E>>,
}

impl<E: Engine> Sha256Hasher<E> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS, use_tables: bool) -> Result<Self, SynthesisError> {
        let table_gadget = if use_tables { Some(Sha256Gadget::new(cs, None, None, false, false, 0, "")?) } else { None };
        Ok(Self { table_gadget })
    }
}

impl<E: Engine> Hasher<E> for Sha256Hasher<E> {
    type Params = ();
    fn hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &[Byte<E>]) -> Result<Vec<Byte<E>>, SynthesisError> {
        match &self.table_gadget {
            Some(gadget) => Ok(gadget.sha256_from_bytes_to_bytes(cs, &input)?.to_vec()),
            None => {
                let inp_bools = bytes_to_bools(cs, input);
                let out_bools = sha256_no_tables(cs, &inp_bools)?;
                bools_to_bytes(cs, &out_bools)
            }
        }
    }

    fn raw_hash(input: &[u8], _params: ()) -> Vec<u8> {
        let mut hasher = Sha256::new();
        hasher.update(input);
        hasher.finalize().to_vec()
    }
}

impl<E: Engine> MerkleCompressor<E, SHA256_DIGEST_NUM_WORDS, SHA256_DIGEST_WORD_SIZE> for Sha256Hasher<E> {
    type Params = ();
    fn compress<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: Sha256Digest<E>, y: Sha256Digest<E>) -> Result<Sha256Digest<E>, SynthesisError> {
        let mut bytes = x.into_le_bytes(cs)?;
        bytes.extend(y.into_le_bytes(cs)?);
        let output = self.hash(cs, &bytes)?;
        Sha256Digest::from_le_bytes(cs, &output)
    }

    fn compress_raw(x: RawSha256Digest<E>, y: RawSha256Digest<E>, params: Self::Params) -> RawSha256Digest<E> {
        let mut bytes = x.to_bytes();
        bytes.extend(y.to_bytes());
        let output = Self::raw_hash(&bytes, params);
        RawSha256Digest::from_bytes::<32>(output.try_into().expect("array size"))
    }
}

pub type Sha256MerkleGadget<'a, E> = MerkleGadget<'a, E, SHA256_DIGEST_NUM_WORDS, SHA256_DIGEST_WORD_SIZE, Sha256Hasher<E>>;