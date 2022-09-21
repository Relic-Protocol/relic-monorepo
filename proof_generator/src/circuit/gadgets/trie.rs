use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

use super::{NumExtension, Nibble, ToNibbles, VarVec, Vecable};
use super::variable_keccak::{RawKeccakDigest, KeccakDigest, KeccakGadget};

const KEY_BYTE_LEN: usize = 32;
type MPTKey<E> = [Byte<E>; KEY_BYTE_LEN];
type RawMPTKey = [u8; KEY_BYTE_LEN];

const KEY_NIBBLE_LEN: usize = KEY_BYTE_LEN * 2;
type KeyNibbleVec<E> = VarVec<E, Nibble<E>, KEY_NIBBLE_LEN>;

fn parse_rlp_str(enc: &[u8]) -> (&[u8], &[u8]) {
    if enc[0] < 0x80 {
        return (&enc[0..1], &enc[1..])
    }
    let (len, offset) = if enc[0] < 0xB8 {
        ((enc[0] - 0x80) as usize, 1 as usize)
    } else {
        let len_size: usize = (enc[0] - 0xB7) as usize;
        let offset = 1 + len_size;
        let mut bytes = [0; 8];
        for i in 0..len_size {
            bytes[8 - len_size + i] = enc[1 + i]
        }
        let len = u64::from_be_bytes(bytes);
        (len as usize, offset)
    };

    (&enc[offset..offset+len], &enc[offset+len..])
}

fn parse_rlp_str_list(enc: &[u8]) -> Vec<&[u8]> {
    assert!(enc[0] >= 0xC0);
    let (len, offset) = if enc[0] < 0xF8 {
        ((enc[0] - 0xC0) as usize, 1 as usize)
    } else {
        let len_size: usize = (enc[0] - 0xF7) as usize;
        let offset = 1 + len_size;
        let mut bytes = [0; 8];
        for i in 0..len_size {
            bytes[8 - len_size + i] = enc[1 + i]
        }
        let len = u64::from_be_bytes(bytes);
        (len as usize, offset)
    };

    let mut list = &enc[offset..offset+len];
    let mut result = vec![];
    while list.len() > 0 {
        let elt;
        (elt, list) = parse_rlp_str(list);
        result.push(elt)
    }
    result
}

fn bytes_to_nibbles<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>]
) -> Result<Vec<Nibble<E>>, SynthesisError> {
    let mut nibbles = Vec::with_capacity(bytes.len()*2);
    for b in bytes {
        nibbles.extend(b.to_be_nibbles(cs)?);
    }
    Ok(nibbles)
}

/*
 * PL = Proof Length (max number of nodes in a proof
 * NL = Node Length (max length of a node in a proof
 */
#[derive(Debug)]
pub struct MPTGadget<E: Engine, const PL: usize, const NL: usize> {
    node_hasher: KeccakGadget<E, 0, NL>,
}

impl<E: Engine, const PL: usize, const NL: usize> MPTGadget<E, PL, NL> {
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS,
    ) -> Result<Self, SynthesisError> {
        let node_hasher = KeccakGadget::new(cs)?;

        Ok(Self { node_hasher})
    }

    fn parse_list< CS:ConstraintSystem<E>>(
        cs: &mut CS,
        bytes: &VarVec<E, Byte<E>, NL>,
    ) -> Result<(Num<E>, VarVec<E, Byte<E>, NL>), SynthesisError> {
        let first = bytes.vals[0].into_num();

        // first handle short lengths (encoded as 0xC0 + len)
        let mut len = first.sub(cs, &Num::Constant(u64_to_ff(0xC0 as u64)))?;

        // if it underflowed, it's not a list
        //constrain_bit_length(cs, &len, 8)?;

        let mut start = Num::one();

        // now handle larger lengths with byte size up to 3
        // (longer lengths cannot exist in ethereum tries)
        for size in 1..4 {
            let size_encoding = Num::Constant(u64_to_ff(0xF7 + size as u64));
            let is_size = Num::equals(cs, &first, &size_encoding)?;
            let supposed_len = Num::from_be_bytes(cs, &bytes.vals[1..1+size])?;
            let this_start = Num::Constant(u64_to_ff(1 + size as u64));

            len = Num::conditionally_select(cs, &is_size, &supposed_len, &len)?;
            start = Num::conditionally_select(cs, &is_size, &this_start, &start)?;
        }

        let list = bytes.suffix(cs, start, Some(4))?;

        Ok((len, list))
    }

    fn parse_branch<CS:ConstraintSystem<E>>(
        cs: &mut CS,
        bytes: &VarVec<E, Byte<E>, NL>,
    ) -> Result<(Boolean, KeccakDigest<E>, VarVec<E, Byte<E>, NL>), SynthesisError> {
        let one = Num::one();

        let first = bytes.vals[0].into_num();
        let hash = KeccakDigest::from_le_bytes(cs, &bytes.vals[1..33])?;
        let mut rest = bytes.suffix(cs, Num::Constant(u64_to_ff(33)), None)?;

        let is_empty = Num::equals(cs, &first, &Num::Constant(u64_to_ff(0x80)))?;
        let empty_rest = bytes.suffix(cs, one, None)?;
        rest = VarVec::conditionally_select(cs, &is_empty, &empty_rest, &rest)?;

        Ok((is_empty, hash, rest))
    }

    fn parse_element<CS:ConstraintSystem<E>>(
        cs: &mut CS,
        bytes: &VarVec<E, Byte<E>, NL>,
    ) -> Result<(VarVec<E, Byte<E>, NL>, VarVec<E, Byte<E>, NL>), SynthesisError> {
        let zero = Num::zero();
        let one = Num::one();

        let first = bytes.vals[0].into_num();

        // string values have first byte in range [0, 0xBF]
        //let check = first.add(cs, &Num::Constant(u64_to_ff(0x40)))?;
        //constrain_bit_length(cs, &check, 8)?;

        // first handle short lengths (encoded as 0x80 + len for len <= 0x37)
        // convenient default because checking the range is hard
        let short_len = first.sub(cs, &Num::Constant(u64_to_ff(0x80 as u64)))?;
        let start = one;
        let mut split_idx = one.add(cs, &short_len)?;
        let mut elt = bytes.slice(cs, start, split_idx)?;

        // now handle small single byte values [0, 0x7F]
        // easy to check high bit
        let bits = first.get_variable().into_bits_le(cs, Some(8))?;
        let is_single = bits[7].not();
        let single_elt =  bytes.slice(cs, zero, one)?;
        elt = VarVec::conditionally_select(cs, &is_single, &single_elt, &elt)?;
        split_idx = Num::conditionally_select(cs, &is_single, &one, &split_idx)?;

        // finally handle larger lengths with byte size up to 3
        // (longer lengths cannot exist in ethereum tries)
        for size in 1..4 {
            let size_encoding = Num::Constant(u64_to_ff(0xB7 + size as u64));
            let is_size = Num::equals(cs, &first, &size_encoding)?;
            let supposed_len = Num::from_be_bytes(cs, &bytes.vals[1..1+size])?;

            let this_start = Num::Constant(u64_to_ff(1 + size as u64));
            let this_split_idx = supposed_len.add(cs, &this_start)?;

            let this_elt = bytes.slice(cs, this_start, this_split_idx)?;
            elt = VarVec::conditionally_select(cs, &is_size, &this_elt, &elt)?;
            split_idx = Num::conditionally_select(cs, &is_size, &this_split_idx, &split_idx)?;
        }

        let rest = bytes.suffix(cs, split_idx, None)?;

        Ok((elt, rest))
    }

    pub fn get_value<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        proof: &VarVec<E, VarVec<E, Byte<E>, NL>, PL>,
        key: MPTKey<E>,
        expected_root: KeccakDigest<E>
    ) -> Result<(Boolean, VarVec<E, Byte<E>, NL>), SynthesisError> {
        let mut key_nibbles = KeyNibbleVec::from(&bytes_to_nibbles(cs, &key)?);
        let one = Num::one();
        let two = one.add(cs, &one)?;

        // initialize result variables
        let mut exists = Boolean::Constant(false);
        let mut value = VarVec::constant(&vec![]);

        let mut expected = expected_root;
        let mut done = Boolean::Constant(false);
        for pi in 0..PL {
            let mut node = proof.vals[pi];

            // check the node's hash is as expected (unless we're done)
            let dgst = self.node_hasher.digest(cs, &node)?;
            KeccakDigest::conditionally_enforce_equal(cs, &done.not(), &dgst, &expected)?;

            // parse out the first two list elements
            let (elt0, elt1);
            (_, node) = Self::parse_list(cs, &node)?;
            (elt0, node) = Self::parse_element(cs, &node)?;
            (elt1, node) = Self::parse_element(cs, &node)?;

            let next_nibble = key_nibbles.vals[0];

            // if the remaining node is empty, then it's a leaf or extension node
            let none_left = node.length().is_zero(cs)?;
            let is_leaf_or_extension = Boolean::and(cs, &done.not(), &none_left)?;
            let is_branch = Boolean::and(cs, &done.not(), &is_leaf_or_extension.not())?;

            // handle leaf + extension cases
            {
                let mut path = elt0;
                let nibbles = path.vals[0].to_be_nibbles(cs)?;
                let flagbits = nibbles[0].as_byte().into_num().into_bits_le(cs, Some(4))?;
                let (is_odd_length, is_leaf) = (
                    Boolean::and(cs, &is_leaf_or_extension, &flagbits[0])?,
                    Boolean::and(cs, &is_leaf_or_extension, &flagbits[1])?
                );
                let is_extension = Boolean::and(cs, &is_leaf_or_extension, &is_leaf.not())?;

                // check the first key nibble if needed
                let first_nibble_equals = Nibble::equals(cs, &next_nibble, &nibbles[1])?;
                let first_nibble_ok = Boolean::or(cs, &first_nibble_equals, &is_odd_length.not())?;

                // skip a key nibble if needed
                key_nibbles = key_nibbles.suffix(cs, Num::from_boolean_is(is_odd_length), Some(1))?;

                path = path.suffix(cs, one, None)?;

                // check if remaining path matches key
                let mut path_nibbles = KeyNibbleVec::from(&bytes_to_nibbles(cs, &path.vals[..KEY_NIBBLE_LEN/2])?);
                path_nibbles.length = path.length().mul(cs, &two)?;
                let path_equals = key_nibbles.starts_with(cs, &path_nibbles)?;

                let keys_equal = Boolean::and(cs, &first_nibble_ok, &path_equals)?;

                // skip past the key nibbles
                let mut skip_offset = Num::from_boolean_is(is_leaf_or_extension);
                skip_offset = skip_offset.mul(cs, &path_nibbles.length)?;
                key_nibbles = key_nibbles.suffix(cs, skip_offset, None)?;

                // handle extension node
                {
                    let equal_and_extension = Boolean::and(cs, &keys_equal, &is_extension)?;
                    Boolean::enforce_equal(cs, &is_extension, &equal_and_extension)?;
                    let next_hash = KeccakDigest::from_le_bytes(cs, &elt1.vals[..32])?;
                    expected = KeccakDigest::conditionally_select(cs, &is_extension, &next_hash, &expected)?;
                }

                // handle leaf node
                {
                    let leaf_good = Boolean::and(cs, &is_leaf, &keys_equal)?;
                    exists = Boolean::or(cs, &exists, &leaf_good)?;
                    value = VarVec::conditionally_select(cs, &exists, &elt1, &value)?;
                    done = Boolean::or(cs, &done, &is_leaf)?;
                }
            }

            // handle branch case
            {
                let mut branches = vec![
                    (elt0.length().is_zero(cs)?, KeccakDigest::from_le_bytes(cs, &elt0.vals[..32])?),
                    (elt1.length().is_zero(cs)?, KeccakDigest::from_le_bytes(cs, &elt1.vals[..32])?),
                ];
                // read remaining elements into vector
                for _ in 2..16 {
                    let (is_empty, hash);
                    (is_empty, hash, node) = Self::parse_branch(cs, &node)?;
                    branches.push((is_empty, hash));
                }
                // check each branch
                for i in 0..16 {
                    let (is_empty, hash) = &branches[i];
                    let is_nibble = Num::equals(cs, &next_nibble.as_byte().into_num(), &Num::Constant(u64_to_ff(i as u64)))?;
                    let mut this_branch = Boolean::and(cs, &is_branch, &is_nibble)?;
                    this_branch = Boolean::and(cs, &this_branch, &done.not())?;

                    let missing = Boolean::and(cs, &this_branch, &is_empty)?;
                    done = Boolean::or(cs, &done, &missing)?;

                    expected = KeccakDigest::conditionally_select(cs, &this_branch, &hash, &expected)?;
                }
                let skipped = key_nibbles.suffix(cs, one, None)?;
                key_nibbles = KeyNibbleVec::conditionally_select(cs, &is_branch, &skipped, &key_nibbles)?;
            }
        }
        Ok((exists, value))
    }

    pub fn get_value_raw(
        &self,
        proof: &Vec<Vec<u8>>,
        key: RawMPTKey,
        expected_root: RawKeccakDigest<E>,
    ) -> (bool, Vec<u8>) {
        let mut expected = expected_root;
        let key = KeccakGadget::<E, 0, NL>::raw_digest(&key).to_bytes();
        let mut key_nibbles: Vec<u8> = key.iter().flat_map(|kb| [kb >> 4, kb & 0xf]).collect();
        for node in proof {
            // first check the hash
            let computed: RawKeccakDigest<E> = KeccakGadget::<E, 0, NL>::raw_digest(&node);
            assert_eq!(computed.words, expected.words);

            // all nodes are RLP lists of strings
            let elts = parse_rlp_str_list(&node);
            if elts.len() == 2 {
                let mut path = elts[0];
                // leaf or extension
                let prefix = path[0] >> 4;
                assert!(prefix < 4);

                if prefix & 1 == 0 {
                    assert_eq!(path[0] & 0xf, 0);
                } else {
                    let next_nibble = key_nibbles.drain(..1).next().unwrap();
                    assert_eq!(path[0] & 0xf, next_nibble);
                }
                path = &path[1..];
                let path_nibbles: Vec<_> = path.iter().flat_map(|kb| [kb >> 4, kb & 0xf]).collect();
                let len = path_nibbles.len();
                let partial_key: Vec<_> = key_nibbles.drain(..len).collect();
                let key_matches = &path_nibbles == &partial_key;

                if prefix & 2 == 0 {
                    // extension node
                    assert!(key_matches);
                    expected = RawKeccakDigest::from_bytes32(elts[1].try_into().unwrap());
                } else {
                    // leaf node
                    if key_matches {
                        return (true, elts[1].to_vec())
                    } else {
                        return (false, vec![])
                    }
                }
            } else {
                // branch node
                assert_eq!(elts.len(), 17);
                let next_nibble = key_nibbles.drain(..1).next().unwrap();

                let branch = elts[next_nibble as usize];
                if branch.len() == 0 {
                    return (false, vec![]);
                } else {
                    expected = RawKeccakDigest::from_bytes32(branch.try_into().unwrap());
                }
            }
        }
        unreachable!();
    }
}

/*
 * PL = Proof Length (max number of nodes in a proof
 * NL = Node Length (max length of a node in a proof
 * KL = Key Length (fixed length of keys before hashing)
 */
#[derive(Debug)]
pub struct SecureMPTGadget<E: Engine, const PL: usize, const NL: usize, const KL: usize> {
    inner: MPTGadget<E, PL, NL>,
    key_hasher: KeccakGadget<E, KL, KL>
}

impl<E: Engine, const PL: usize, const NL: usize, const KL: usize> SecureMPTGadget<E, PL, NL, KL> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let inner = MPTGadget::new(cs)?;
        let key_hasher = KeccakGadget::new(cs)?;
        Ok(Self { inner, key_hasher })
    }

    pub fn get_value<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        proof: &VarVec<E, VarVec<E, Byte<E>, NL>, PL>,
        key: [Byte<E>; KL],
        expected_root: KeccakDigest<E>
    ) -> Result<(Boolean, VarVec<E, Byte<E>, NL>), SynthesisError> {
        let key = self.key_hasher.digest(cs, &key.into())?.into_le_bytes(cs)?;
        self.inner.get_value(cs, proof, key.try_into().unwrap(), expected_root)
    }

    pub fn get_value_raw(
        &self,
        proof: &Vec<Vec<u8>>,
        key: RawMPTKey,
        expected_root: RawKeccakDigest<E>,
    ) -> (bool, Vec<u8>) {
        let key = KeccakGadget::<E, 0, NL>::raw_digest(&key).to_bytes();
        self.inner.get_value_raw(proof, key.try_into().unwrap(), expected_root)
    }
}
