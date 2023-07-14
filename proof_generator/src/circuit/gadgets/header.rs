use std::marker::PhantomData;

use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::{Byte, IntoBytes};
use franklin_crypto::plonk::circuit::allocated_num::{AllocatedNum, Num};
use franklin_crypto::plonk::circuit::channel::ChannelGadget;
use franklin_crypto::jive::JiveEngine;
use franklin_crypto::bellman::Field;
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

use super::merkle::MerkleGadget;
use super::utils::bounded::Bounds;
use super::utils::num::NumExtension;
use super::utils::rlc::RLCGadget;
use super::utils::rlp::{RLPGadget, encoded_list_bounds, RLPDataResult};
use super::utils::vec::{VarVec, Vecable};
use super::variable_jive::{JiveGadget, JiveDigest, RawJiveDigest, JiveMerkleGadget};
use super::variable_keccak::{KeccakDigest, KeccakGadget, RawKeccakDigest};

use ::rlp;

pub enum HeaderField {
    ParentHash,
    OmnersHash,
    Beneficiary,
    StateRoot,
    TransactionsRoot,
    ReceiptsRoot,
    LogsBloom,
    Difficulty,
    Number,
    GasLimit,
    GasUsed,
    Timestamp,
    ExtraData,
    MixHash,
    Nonce,
    BaseFee,
    WithdrawalsRoot,
    Reserved, // extra reserved field, for forward compatibility with any future updates
}

pub const BASE_HEADER_RLP_FIELDS: [Bounds; 15] = [
    Bounds::new(32, 32),
    Bounds::new(32, 32),
    Bounds::new(20, 20),
    Bounds::new(32, 32),
    Bounds::new(32, 32),
    Bounds::new(32, 32),
    Bounds::new(256, 256),
    Bounds::new(0, 8),
    Bounds::new(0, 8),
    Bounds::new(0, 8),
    Bounds::new(0, 8),
    Bounds::new(0, 8),
    Bounds::new(0, 32),
    Bounds::new(32, 32),
    Bounds::new(8, 8),
];

pub const EXTRA_HEADER_RLP_FIELDS: [Bounds; 3] = [
    Bounds::new(0, 8),
    Bounds::new(32, 32),

    // extra reserved field, for forward compatibility with any future updates
    // the size was chosen as large as possible, without increasing the number
    // of keccak rounds required to hash a header
    Bounds::new(0, 67)
];

pub type BlockHeaderHasher<E> = KeccakGadget<E>;
pub type BlockHeaderVec<E> = VarVec<E, Byte<E>>;

impl<E: Engine> BlockHeaderVec<E> {
    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<Vec<u8>>) -> Result<Self, SynthesisError> {
        let bounds = encoded_list_bounds(&BASE_HEADER_RLP_FIELDS, &EXTRA_HEADER_RLP_FIELDS);
        VarVec::alloc_with_bounds(cs, bounds, value.as_ref().map(Vec::as_slice))
    }
}

#[derive(Clone)]
pub struct RawParsedField<E: Engine> {
    data: Vec<u8>,
    exists: bool,
    engine: PhantomData<E>
}

impl<E: Engine> RawParsedField<E> {
    pub fn new(data: Vec<u8>, exists: bool) -> Self {
        Self { data, exists, engine: PhantomData }
    }

    pub fn missing() -> Self {
        Self { data: vec![], exists: false, engine: PhantomData }
    }

    pub fn merkle_leaf_data(&self) -> Vec<u8> {
        let data = if self.exists { self.data.as_slice() } else { &[] };
        let prefix = if self.exists { 1_u8 } else { 0_u8 };
        std::iter::once(prefix).chain(data.iter().map(|v| *v)).collect()
    }
}

pub struct RawParsedHeader<E: Engine> {
    pub fields: Vec<RawParsedField<E>>,
    engine: PhantomData<E>
}

fn bytes_to_fe<E: Engine>(bytes: &[u8]) -> E::Fr {
    let mult = u64_to_ff(256);
    let mut res = E::Fr::zero();
    for byte in bytes {
        res.mul_assign(&mult);
        res.add_assign(&u64_to_ff(*byte as u64));
    }
    res
}

// TODO: allow specifying header fields by type, implement the getters with macros
impl<E: Engine> RawParsedHeader<E> {
    pub fn parent_hash(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::ParentHash as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn omners_hash(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::OmnersHash as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn beneficiary(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::Beneficiary as usize].data)
    }

    pub fn state_root(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::StateRoot as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn transactions_root(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::TransactionsRoot as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn receipts_root(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::ReceiptsRoot as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn logs_bloom(&self) -> Vec<u8> {
        self.fields[HeaderField::LogsBloom as usize].data.clone()
    }

    pub fn difficulty(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::Difficulty as usize].data)
    }

    pub fn number(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::Number as usize].data)
    }

    pub fn gas_limit(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::GasLimit as usize].data)
    }

    pub fn gas_used(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::GasUsed as usize].data)
    }

    pub fn timestamp(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::Timestamp as usize].data)
    }

    pub fn extra_data(&self) -> Vec<u8> {
        self.fields[HeaderField::ExtraData as usize as usize].data.clone()
    }

    pub fn mix_hash(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::MixHash as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    pub fn nonce(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::Nonce as usize].data)
    }

    pub fn base_fee(&self) -> E::Fr {
        bytes_to_fe::<E>(&self.fields[HeaderField::BaseFee as usize].data)
    }

    pub fn withdrawals_root(&self) -> RawKeccakDigest<E> {
        RawKeccakDigest::from_bytes::<32>(self.fields[HeaderField::WithdrawalsRoot as usize].data.as_slice().try_into().expect("invalid hash size"))
    }

    fn merkle_leaves(
        &self,
        params: &E::Params,
    ) -> Vec<RawJiveDigest<E>>
        where E: JiveEngine
    {
        let missing_hash = JiveGadget::raw_digest(&RawParsedField::<E>::missing().merkle_leaf_data(), params);
        let num_fields = BASE_HEADER_RLP_FIELDS.len() + EXTRA_HEADER_RLP_FIELDS.len();
        let pad_len = (num_fields as u64).next_power_of_two() as usize - num_fields;
        let mut leaves = self.fields.iter()
            .map(|f| JiveGadget::raw_digest(&f.merkle_leaf_data(), params))
            .collect::<Vec<_>>();
        leaves.extend(std::iter::from_fn(|| Some(missing_hash.clone())).take(pad_len));
        leaves
    }

    pub fn merkle_proof(
        &self,
        index: usize,
        params: &E::Params,
    ) -> Vec<RawJiveDigest<E>>
        where E: JiveEngine
    {
        let leaves = self.merkle_leaves(params);
        JiveMerkleGadget::raw_compute_proof(index, leaves, params)
    }
}

pub struct ParsedField<E: Engine> {
    data: VarVec<E, Byte<E>>,
    exists: Boolean
}

impl<E: Engine> ParsedField<E> {
    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, bounds: Bounds, value: Option<RawParsedField<E>>) -> Result<Self, SynthesisError> {
        let data = VarVec::alloc_with_bounds(cs, bounds, value.as_ref().map(|v| v.data.as_slice()))?;
        let exists = Boolean::alloc(cs, value.as_ref().map(|v| v.exists))?;
        Ok(Self { data, exists })
    }

    pub fn from_rlp(rlp: RLPDataResult<E>) -> Self {
        Self { data: rlp.data, exists: rlp.exists }
    }

    pub fn missing() -> Self {
        Self { data: VarVec::from(&[]), exists: Boolean::constant(false)}
    }

    pub fn merkle_leaf_data<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS
    ) -> Result<VarVec<E, Byte<E>>, SynthesisError> {
        let value = VarVec::conditionally_select(cs, &self.exists, &self.data, &VarVec::from(&[]))?;
        let prefix: Byte<E> = Byte::conditionally_select(cs, &self.exists, &Byte::constant(1), &Byte::constant(0))?;
        value.prepend(cs, &[prefix])
    }

    pub fn constant(raw: RawParsedField<E>) -> Self {
        Self { data: VarVec::constant(raw.data), exists: Boolean::constant(raw.exists) }
    }
}

pub struct ParsedHeader<E: Engine> {
    fields: Vec<ParsedField<E>>
}

// TODO: allow specifying header fields by type, implement the getters with macros
impl<E: Engine> ParsedHeader<E> {
    pub fn parent_hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::ParentHash as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    pub fn omners_hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::OmnersHash as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    pub fn beneficiary<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::Beneficiary as usize].data;
        data.to_num(cs)
    }

    pub fn state_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::StateRoot as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    pub fn transactions_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::TransactionsRoot as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    pub fn receipts_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::ReceiptsRoot as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    // TODO: improve return type
    pub fn logs_bloom<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<VarVec<E, Byte<E>>, SynthesisError> {
        let data = &self.fields[HeaderField::LogsBloom as usize].data;
        Ok(data.clone())
    }

    pub fn difficulty<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::Difficulty as usize].data;
        data.to_num(cs)
    }

    pub fn number<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::Number as usize].data;
        data.to_num(cs)
    }

    pub fn gas_limit<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::GasLimit as usize].data;
        data.to_num(cs)
    }

    pub fn gas_used<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::GasUsed as usize].data;
        data.to_num(cs)
    }

    pub fn timestamp<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::Timestamp as usize].data;
        data.to_num(cs)
    }

    pub fn extra_data<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<VarVec<E, Byte<E>>, SynthesisError> {
        let data = &self.fields[HeaderField::ExtraData as usize].data;
        Ok(data.clone())
    }

    pub fn mix_hash<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::MixHash as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    pub fn nonce<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::Nonce as usize].data;
        data.to_num(cs)
    }

    pub fn base_fee<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let data = &self.fields[HeaderField::BaseFee as usize].data;
        data.to_num(cs)
    }

    pub fn withdrawals_root<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<KeccakDigest<E>, SynthesisError> {
        let data = &self.fields[HeaderField::WithdrawalsRoot as usize].data;
        KeccakDigest::from_le_bytes(cs, data.vals())
    }

    fn merkle_leaves<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        gadget: &JiveGadget<E>
    ) -> Result<Vec<JiveDigest<E>>, SynthesisError>
        where E: JiveEngine
    {
        let missing_data = ParsedField::missing().merkle_leaf_data(cs)?;
        let missing_hash = gadget.digest(cs, &missing_data)?;
        let num_fields = BASE_HEADER_RLP_FIELDS.len() + EXTRA_HEADER_RLP_FIELDS.len();
        let pad_len = (num_fields as u64).next_power_of_two() as usize - num_fields;
        let mut leaves = self.fields.iter()
            .map(|f| {
                let data = f.merkle_leaf_data(cs)?;
                gadget.digest(cs, &data)
            })
            .collect::<Result<Vec<_>, _>>()?;
        leaves.extend(std::iter::from_fn(|| Some(missing_hash.clone())).take(pad_len));
        Ok(leaves)
    }

    pub fn merkle_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        gadget: &JiveGadget<E>
    ) -> Result<JiveDigest<E>, SynthesisError>
        where E: JiveEngine
    {
        let merkle = MerkleGadget::new(gadget);
        let leaves = self.merkle_leaves(cs, gadget)?;
        merkle.merkle_root(cs, leaves)
    }

    pub fn recompute_root<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        gadget: &JiveGadget<E>,
        idx: Num<E>,
        field: &ParsedField<E>,
        proof: Option<&Vec<RawJiveDigest<E>>>,
    ) -> Result<JiveDigest<E>, SynthesisError>
        where E: JiveEngine
    {
        let num_fields = BASE_HEADER_RLP_FIELDS.len() + EXTRA_HEADER_RLP_FIELDS.len();
        let proof_len = (num_fields as u64).next_power_of_two().ilog2() as usize;
        let proof = (0..proof_len)
            .map(|i| JiveDigest::alloc(cs, proof.map(|p| p[i])))
            .collect::<Result<Vec<_>, _>>()?;
        let merkle = MerkleGadget::new(gadget);
        let data = field.merkle_leaf_data(cs)?;
        let hash = gadget.digest(cs, &data)?;
        merkle.recompute_root(cs, idx, hash, &proof)
    }
}

pub fn parse_header<E: Engine, C: ChannelGadget<E>, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    rlc: &mut RLCGadget<E, C>,
    header: &VarVec<E, Byte<E>>
) -> Result<ParsedHeader<E>, SynthesisError> {
    let mut fields = RLPGadget::new().parse_list(cs, &BASE_HEADER_RLP_FIELDS, &EXTRA_HEADER_RLP_FIELDS, header)?;
    rlc.constrain_rlc(cs, &fields, header)?;
    let fields: Vec<ParsedField<E>> = fields.field_results.drain(..).map(ParsedField::from_rlp).collect();
    Ok(ParsedHeader { fields })
}

pub fn raw_parse_header<E: Engine> (
    header: &Vec<u8>
) -> RawParsedHeader<E> {
    let mut list_result: Vec<Vec<u8>> = rlp::decode_list(header.as_slice());
    let mut fields: Vec<_> = list_result.drain(..).map(|data| RawParsedField::new(data, true)).collect();
    let mut offset = BASE_HEADER_RLP_FIELDS.len();
    assert!(fields.len() >= offset);
    for extra in EXTRA_HEADER_RLP_FIELDS {
        offset += 1;
        if fields.len() < offset {
            let data = std::iter::repeat(0_u8).take(extra.lower).collect();
            let exists = false;
            fields.push(RawParsedField::new(data, exists));
        }
    }
    RawParsedHeader { fields, engine: PhantomData }
}

pub const FACTOR: usize = 1000000000;

#[derive(Clone,Copy,Debug)]
pub struct RawBaseFeeStats<E: Engine> {
    cumulative: E::Fr,
    cumulative_2: E::Fr,
    cumulative_3: E::Fr,
    cumulative_4: E::Fr
}

impl<E: Engine> RawBaseFeeStats<E> {
    pub fn encode_words(&self) -> [E::Fr; 4] {
        [self.cumulative, self.cumulative_2, self.cumulative_3, self.cumulative_4]
    }

    pub fn parse_words(words: &[E::Fr]) -> (Self, &[E::Fr]) {
        let cumulative = words[0];
        let cumulative_2 = words[1];
        let cumulative_3 = words[2];
        let cumulative_4 = words[3];
        (
            Self { cumulative, cumulative_2, cumulative_3, cumulative_4 },
            &words[4..]
        )
    }
}

impl<E: Engine> Default for RawBaseFeeStats<E> {
    fn default() -> Self {
        Self { cumulative: E::Fr::zero(), cumulative_2: E::Fr::zero(), cumulative_3: E::Fr::zero(), cumulative_4: E::Fr::zero() }
    }
}

#[derive(Clone,Copy,Debug)]
pub struct BaseFeeStats<E: Engine> {
    cumulative: Num<E>,
    cumulative_2: Num<E>,
    cumulative_3: Num<E>,
    cumulative_4: Num<E>
}

impl<E: Engine> BaseFeeStats<E> {
    pub const NUM_VARIABLES: usize = 4;

    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<RawBaseFeeStats<E>>) -> Result<Self, SynthesisError> {
        Ok(Self {
            cumulative: Num::alloc(cs, value.map(|v| v.cumulative))?,
            cumulative_2: Num::alloc(cs, value.map(|v| v.cumulative_2))?,
            cumulative_3: Num::alloc(cs, value.map(|v| v.cumulative_3))?,
            cumulative_4: Num::alloc(cs, value.map(|v| v.cumulative_4))?,
        })
    }

    pub fn inputize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.cumulative.inputize(cs)?;
        self.cumulative_2.inputize(cs)?;
        self.cumulative_3.inputize(cs)?;
        self.cumulative_4.inputize(cs)
    }

    pub fn alloc_input<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<RawBaseFeeStats<E>>) -> Result<Self, SynthesisError> {
        let res = Self::alloc(cs, value)?;
        res.inputize(cs)?;
        Ok(res)
    }

    pub fn update<CS: ConstraintSystem<E>>(&self, cs: &mut CS, base_fee: Num<E>) -> Result<Self, SynthesisError> {
        let Self { mut cumulative, mut cumulative_2, mut cumulative_3, mut cumulative_4} = self;

        let mut tmp = base_fee.clone();
        cumulative = cumulative.add(cs, &tmp)?;
        tmp = tmp.mul(cs, &base_fee)?;
        (tmp, _) = tmp.divmod(cs, FACTOR)?;
        cumulative_2 = cumulative_2.add(cs, &tmp)?;
        tmp = tmp.mul(cs, &base_fee)?;
        (tmp, _) = tmp.divmod(cs, FACTOR)?;
        cumulative_3 = cumulative_3.add(cs, &tmp)?;
        tmp = tmp.mul(cs, &base_fee)?;
        (tmp, _) = tmp.divmod(cs, FACTOR)?;
        cumulative_4 = cumulative_4.add(cs, &tmp)?;

        Ok(Self { cumulative, cumulative_2, cumulative_3, cumulative_4 })
    }

    pub fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError> {
        self.cumulative.enforce_equal(cs, &other.cumulative)?;
        self.cumulative_2.enforce_equal(cs, &other.cumulative_2)?;
        self.cumulative_3.enforce_equal(cs, &other.cumulative_3)?;
        self.cumulative_4.enforce_equal(cs, &other.cumulative_4)
    }

    pub fn get_value(&self) -> Option<RawBaseFeeStats<E>> {
        self.cumulative.get_value().map(|cbf| {
            RawBaseFeeStats {
                cumulative: cbf,
                cumulative_2: self.cumulative_2.get_value().unwrap(),
                cumulative_3: self.cumulative_3.get_value().unwrap(),
                cumulative_4: self.cumulative_4.get_value().unwrap(),
            }
        })
    }

    pub fn encode_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut result = self.cumulative.into_be_bytes(cs)?;
        result.extend(self.cumulative_2.into_be_bytes(cs)?);
        result.extend(self.cumulative_3.into_be_bytes(cs)?);
        result.extend(self.cumulative_4.into_be_bytes(cs)?);
        Ok(result)
    }

    pub fn encode_words(&self) -> [Num<E>; 4] {
        [self.cumulative, self.cumulative_2, self.cumulative_3, self.cumulative_4]
    }

    pub fn parse_words(allocated_nums: &[AllocatedNum<E>]) -> (Self, &[AllocatedNum<E>]) {
        let cumulative = Num::Variable(allocated_nums[0]);
        let cumulative_2 = Num::Variable(allocated_nums[1]);
        let cumulative_3 = Num::Variable(allocated_nums[2]);
        let cumulative_4 = Num::Variable(allocated_nums[3]);
        (
            Self { cumulative, cumulative_2, cumulative_3, cumulative_4 },
            &allocated_nums[4..]
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;
    use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;
    use franklin_crypto::bellman::pairing::bn256::Bn256;

    const BLOCK_HEADER_0: &'static str = "f90214a00000000000000000000000000000000000000000000000000000000000000000a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347940000000000000000000000000000000000000000a0d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421b9010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000850400000000808213888080a011bbe8db4e347b4e8c937c1c8370e4b5ed33adb3db69cbdb7a38e1e50b1b82faa00000000000000000000000000000000000000000000000000000000000000000880000000000000042";
    const BLOCK_HEADER_1: &'static str = "f90211a0d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d493479405a56e2d52c817161883f50c441c3228cfe54d9fa0d67e4d450343046425ae4271474353857ab860dbc0a1dde64b41b5cd3a532bf3a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008503ff80000001821388808455ba422499476574682f76312e302e302f6c696e75782f676f312e342e32a0969b900de27b6ac6a67742365dd65f55a0526c41fd18e1b16f1a1215c2e66f5988539bd4979fef1ec4";
    const BLOCK_HEADER_17000000: &'static str = "f90211a0e464691f28218637d00ac4d694a86c0e01044b0a76b357b997e575be6d4cc135a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d4934794690b9a9e9aa1c9db991c7721a92d351db4fac990a072eea852168e4156811869d6e40789083891288161d5a110259cf4fc922b1a09a006ca3364e7ff05c6adad066d09dd50edc25e7935a7aa0bdb2f4ce07d2f5bf82ea0dafc7e17d609503a08b1406eb69c714cb3e7ba51e84580977c449999068ae513b9010000a5800311003514143110248118186108f900001a860055664930042204b7b9180823e91008c0b9131b71049561150a820741c69ac129022612639111ea2d3d64486012650ac92cef32730c52d000709735a2c81040099802121c448a70424a2342048632438001181c100001478f58a61c2006889926009a20035810b90034031189704c211210f15546029a8018c704609505b1a2034c0e3a824b4015b722cb4d01478131794a0ad270ab09108c102c49805860b10a0332111902920100834dd80582381a211238810814560a259d414c4b00240a70d0047e5d2a154ee4462230aa599280a9808624b042218981518f3400390b4c827819459d69e1501c008084010366408401c9c380838bc84a846430ae138f627920406275696c64657230783639a0508cf9f7faca2553230266065ff45109c2a25c2a55138f4176fd5228a7339b778800000000000000008504cad3abe1";

    #[test]
    fn test_header_parsing_and_merklization() {
        type E = Bn256;
        let mut assembly = TrivialAssembly::<E, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>::new();
        let cs = &mut assembly;
        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        use franklin_crypto::plonk::circuit::channel::JiveChannelGadget;
        use franklin_crypto::jive::bn256::Bn256JiveParams;
        use super::super::variable_jive::JiveGadget;
        let params = Bn256JiveParams::new(true);
        let mut rlc: RLCGadget<E, JiveChannelGadget<E>> = RLCGadget::new(&params);
        let jive_gadget = JiveGadget::new(&params);

        for raw in [BLOCK_HEADER_0, BLOCK_HEADER_1, BLOCK_HEADER_17000000] {
            let block_header = hex::decode(raw).unwrap();
            let header = BlockHeaderVec::alloc(cs, Some(block_header.clone())).unwrap();

            let result = parse_header(cs, &mut rlc, &header).unwrap();
            let raw_result = raw_parse_header::<E>(&block_header);

            result.number(cs).unwrap().enforce_equal(cs, &Num::Constant(raw_result.number())).unwrap();
            result.timestamp(cs).unwrap().enforce_equal(cs, &Num::Constant(raw_result.timestamp())).unwrap();
            result.parent_hash(cs).unwrap().enforce_equal(cs, &KeccakDigest::constant(raw_result.parent_hash())).unwrap();
            result.beneficiary(cs).unwrap().enforce_equal(cs, &Num::Constant(raw_result.beneficiary())).unwrap();
            result.state_root(cs).unwrap().enforce_equal(cs, &KeccakDigest::constant(raw_result.state_root())).unwrap();
            result.transactions_root(cs).unwrap().enforce_equal(cs, &KeccakDigest::constant(raw_result.transactions_root())).unwrap();
            result.nonce(cs).unwrap().enforce_equal(cs, &Num::Constant(raw_result.nonce())).unwrap();

            let root = result.merkle_root(cs, &jive_gadget).unwrap();
            for index in [HeaderField::StateRoot as usize, HeaderField::BaseFee as usize] {
                let proof = raw_result.merkle_proof(index, &params);

                let recomputed = ParsedHeader::recompute_root(
                    cs,
                    &jive_gadget,
                    Num::Constant(u64_to_ff(index as u64)),
                    &result.fields[index],
                    Some(&proof)
                ).unwrap();

                root.enforce_equal(cs, &recomputed).unwrap();
            }
        }

        // finalize all rlp constraints
        rlc.finalize(cs).unwrap();

        println!("{} steps", assembly.get_current_step_number());

        assembly.finalize();

        println!("{} gates", assembly.n());
    }
}