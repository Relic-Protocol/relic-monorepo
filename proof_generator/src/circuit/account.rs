use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof;
use franklin_crypto::bellman::plonk::better_better_cs::setup::{VerificationKey, Setup};
use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::boolean::Boolean;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::bellman::worker::Worker;
use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;

use super::gadgets::merkle::{MerkleDigest, MerkleGadget, RawMerkleDigest};
use super::gadgets::header::{BlockHeaderHasher, BlockHeaderVec, extract_state_root};
use super::gadgets::account::{ADDRESS_SIZE, AccountTrieGadget, ProofVec};
use franklin_crypto::plonk::circuit::hashes_with_tables::utils::u64_to_ff;

use std::marker::PhantomData;

#[derive(Debug)]
pub struct EthereumAccountCircuit<E:Engine>{
    account: Option<[u8; ADDRESS_SIZE]>,
    account_proof: Option<Vec<Vec<u8>>>,

    header: Option<Vec<u8>>,
    header_proof: Option<Vec<Vec<u8>>>,
    header_idx: Option<usize>,
    merkle_root: Option<Vec<u8>>,
    merkle_depth: usize,

    engine: PhantomData<E>,
}

impl<E: Engine> Circuit<E> for EthereumAccountCircuit<E> {
    type MainGate = Width4MainGateWithDNext;

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(
            vec![
                Width4MainGateWithDNext::default().into_internal(),
            ]
        )
    }

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>
    {
        let header = BlockHeaderVec::alloc(cs, self.header.as_ref().map(Vec::as_slice))?;

        // verify block header is in merkle tree
        {
            let hasher: BlockHeaderHasher<E> = BlockHeaderHasher::new(cs)?;
            let hash = hasher.digest(cs, &header)?;

            let merkle_gadget: MerkleGadget<E> = MerkleGadget::new(cs, true)?;
            let merkle_root: MerkleDigest<E> = MerkleDigest::alloc_input(
                cs,
                self.merkle_root.as_ref().map(|r| RawMerkleDigest::from_bytes32(r.as_slice().try_into().expect("unexpected size")))
            )?;
            let idx = Num::alloc(cs, self.header_idx.map(|idx| u64_to_ff(idx as u64)))?;
            let value = hash.into_le_bytes(cs)?;
            let proof = (0..self.merkle_depth).map(
                |i| (0..32).map(
                    |j| {
                        let value = self.header_proof.as_ref().map(|proof| proof[i][j]);
                        let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
                        Byte::from_num(cs, num)
                    }
                ).collect::<Result<Vec<_>, _>>()
            ).collect::<Result<Vec<_>, _>>()?;

            merkle_gadget.verify(cs, merkle_root, idx, &value, &proof)?;
        }

        // take account trie root from header
        let account_root = extract_state_root(cs, &header)?;

        // verify trie value
        {
            let trie_gadget: AccountTrieGadget<E> = AccountTrieGadget::new(cs)?;
            let key: [Byte<E>; ADDRESS_SIZE] = (0..ADDRESS_SIZE).map(
                |i| {
                    let value = self.account.as_ref().map(|addr| addr[i]);
                    let num = Num::alloc(cs, value.map(|v| u64_to_ff(v as u64)))?;
                    Byte::from_num(cs, num)
                }
            ).collect::<Result<Vec<_>, _>>()?.try_into().expect("unexpected size");

            let proof = ProofVec::alloc(cs, self.account_proof.as_ref().map(Vec::as_slice))?;
            let (exists, value) = trie_gadget.get_value(
                cs,
                &proof,
                key,
                account_root
            )?;
            Boolean::enforce_equal(cs, &exists, &Boolean::Constant(true))?;

            // TODO: probably convert this to a smaller input
            value.inputize(cs)?;
        }

        Ok(())
    }
}

pub fn create_account_circuit_setup<E: Engine>(
    worker: &Worker,
    merkle_depth: usize,
) -> Result<Setup<E, EthereumAccountCircuit<E>>, SynthesisError> {
    let circuit = EthereumAccountCircuit{
        account: None,
        account_proof: None,
        header: None,
        header_proof: None,
        header_idx: None,
        merkle_root: None,
        merkle_depth,
        engine: PhantomData,
    };
    let mut assembly = SetupAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    circuit.synthesize(&mut assembly)?;
    println!("Using {} gates", assembly.n());
    assembly.finalize();
    println!("Using {} gates (final)", assembly.n());
    assembly.create_setup(worker)
}

pub fn create_account_circuit_vk<E: Engine>(
    worker: &Worker,
    setup: &Setup<E, EthereumAccountCircuit<E>>,
    crs: &Crs<E, CrsForMonomialForm>,
) -> Result<VerificationKey<E, EthereumAccountCircuit<E>>, SynthesisError> {
    VerificationKey::<E, EthereumAccountCircuit<E>>::from_setup(setup, worker, crs)
}

pub fn create_account_circuit_proof<E: Engine, T: Transcript<E::Fr>>(
    worker: &Worker,
    crs: &Crs<E, CrsForMonomialForm>,
    vk: &VerificationKey<E, EthereumAccountCircuit<E>>,
    setup: &Setup<E, EthereumAccountCircuit<E>>,
    transcript_params: Option<T::InitializationParameters>,
    account: [u8; ADDRESS_SIZE],
    account_proof: &Vec<Vec<u8>>,
    header: &Vec<u8>,
    header_proof: &Vec<Vec<u8>>,
    header_idx: usize,
    merkle_root: &Vec<u8>,
    merkle_depth: usize,
) -> Result<Proof<E, EthereumAccountCircuit<E>>, SynthesisError> {
    let mut assembly = ProvingAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    {
        let circuit = EthereumAccountCircuit::<E>{
            account: Some(account.clone()),
            account_proof: Some(account_proof.clone()),
            header: Some(header.clone()),
            header_proof: Some(header_proof.clone()),
            header_idx: Some(header_idx),
            merkle_root: Some(merkle_root.clone()),
            merkle_depth,
            engine: PhantomData,
        };
        circuit.synthesize(&mut assembly).expect("synthesize failed");
    }
    assembly.finalize();

    let proof = assembly.create_proof::<EthereumAccountCircuit<E>, T>(
        worker,
        setup,
        crs,
        transcript_params.clone()
    )?;

    let is_valid = verify::<_, _, T>(vk, &proof, transcript_params)?;
    assert!(is_valid);

    Ok(proof)
}
