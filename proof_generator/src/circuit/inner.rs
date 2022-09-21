use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof;
use franklin_crypto::bellman::plonk::better_better_cs::setup::{VerificationKey, Setup};
use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::plonk::circuit::byte::Byte;
use franklin_crypto::bellman::worker::Worker;
use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;

use super::gadgets::NumExtension;
use super::gadgets::merkle::{MerkleDigest, MerkleGadget};
use super::gadgets::variable_keccak::{RawKeccakDigest, KeccakDigest};
use super::gadgets::header::{BlockHeaderHasher, BlockHeaderVec};

use std::marker::PhantomData;

#[derive(Debug)]
pub struct EthereumBlockHeaderCircuit<E:Engine>{
    num_headers: usize,
    headers: Option<Vec<Vec<u8>>>,
    engine: PhantomData<E>,
}

impl<E:Engine> EthereumBlockHeaderCircuit<E> {
    pub const NUM_INPUTS: usize = 2 * KeccakDigest::<E>::NUM_VARIABLES + MerkleDigest::<E>::NUM_VARIABLES;
}

impl<E: Engine> Circuit<E> for EthereumBlockHeaderCircuit<E> {
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
        if let Some(headers) = &self.headers {
            assert_eq!(self.num_headers, headers.len());
        }

        let hasher: BlockHeaderHasher<E> = BlockHeaderHasher::new(cs)?;
        let mut hashes = Vec::with_capacity(self.num_headers);
        let mut hashes_raw = self.headers.as_ref().map(|_| Vec::with_capacity(self.num_headers));
        let mut parent_hashes = Vec::with_capacity(self.num_headers);
        let mut parent_hashes_raw = self.headers.as_ref().map(|_| Vec::with_capacity(self.num_headers));

        for idx in 0..self.num_headers {
            let header = self.headers.as_ref().map(|headers| &headers[idx]);
            if let Some(header) = header {
                // compute raw block hash
                hashes_raw.as_mut().unwrap().push(BlockHeaderHasher::<E>::raw_digest(header));

                // pull out parent hash from header
                // parent hash starts 4 bytes into the header
                let parent_hash = RawKeccakDigest::from_bytes32(header[4..36].try_into().unwrap());
                parent_hashes_raw.as_mut().unwrap().push(parent_hash);
            }

            let header_bytes = BlockHeaderVec::alloc(cs, header.map(Vec::as_slice))?;
            hashes.push(hasher.digest(cs, &header_bytes)?);

            // parent hash is the first RLP element in the block header
            // at byte offset 4, so we'll compare 32bit chunks
            let parent_digest_words = header_bytes.vals()[4..36]
                .chunks(8)
                .map(|chunk| Num::from_le_bytes(cs, chunk))
                .collect::<Result<Vec<_>,_>>()?;
            parent_hashes.push(KeccakDigest::parse_digest_nums(parent_digest_words.as_slice()).0);
        }

        // verify first parent hash
        let first = KeccakDigest::alloc_input(cs, parent_hashes_raw.map(|dgsts| dgsts[0]))?;
        first.enforce_equal(cs, &parent_hashes[0])?;

        // verify outputs
        for idx in 1..self.num_headers {
            parent_hashes[idx].enforce_equal(cs, &hashes[idx-1])?;
        }

        // verify last digest
        let last = KeccakDigest::alloc_input(cs, hashes_raw.as_ref().map(|hs| *hs.last().unwrap()))?;
        last.enforce_equal(cs, &hashes.last().unwrap())?;

        // verify merkle tree root
        {
            let leaves: Vec<Vec<Byte<E>>> = hashes.iter().map(|h| h.into_le_bytes(cs)).collect::<Result<Vec<_>,_>>()?;
            let leaves_raw: Option<Vec<Vec<u8>>> = hashes_raw.map(|hashes| hashes.iter().map(|h| h.to_bytes()).collect());
            let merkle_gadget = MerkleGadget::new(cs, true)?;
            let root = merkle_gadget.merkle_root(cs, leaves)?;
            let root_raw = MerkleDigest::alloc_input(cs, leaves_raw.map(MerkleGadget::<E>::raw_merkle_root))?;
            root.enforce_equal(cs, &root_raw)?;
        }

        // XXX force circuit to contain a multiply gate to avoid zero points
        let var = cs.alloc(|| { Ok(E::Fr::zero()) })?;
        let mut gate_term = MainGateTerm::new();

        let mut multiplicative_term = ArithmeticTerm::from_variable(var);
        multiplicative_term = multiplicative_term.mul_by_variable(var);
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(var));

        cs.allocate_main_gate(gate_term)?;

        Ok(())
    }
}

pub fn create_inner_circuit_setup<E: Engine>(
    worker: &Worker,
    num_headers: usize
) -> Result<Setup<E, EthereumBlockHeaderCircuit<E>>, SynthesisError> {
    let circuit = EthereumBlockHeaderCircuit{
        num_headers,
        headers: None,
        engine: PhantomData,
    };
    let mut assembly = SetupAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    circuit.synthesize(&mut assembly)?;
    println!("Using {} gates", assembly.n());
    assembly.finalize();
    println!("Using {} gates (final)", assembly.n());
    assembly.create_setup(worker)
}

pub fn create_inner_circuit_vk<'a, E: Engine>(
    worker: &Worker,
    setup: Setup<E, EthereumBlockHeaderCircuit<E>>,
    crs: &Crs<E, CrsForMonomialForm>,
) -> Result<VerificationKey<E, EthereumBlockHeaderCircuit<E>>, SynthesisError> {
    VerificationKey::<E, EthereumBlockHeaderCircuit<E>>::from_setup(&setup, worker, crs)
}

pub fn create_inner_circuit_proof<'a, E: Engine, T: Transcript<E::Fr>>(
    worker: &Worker,
    crs: &Crs<E, CrsForMonomialForm>,
    vk: &VerificationKey<E, EthereumBlockHeaderCircuit<E>>,
    setup: &Setup<E, EthereumBlockHeaderCircuit<E>>,
    transcript_params: Option<T::InitializationParameters>,
    headers: &Vec<Vec<u8>>,
) -> Result<Proof<E, EthereumBlockHeaderCircuit<E>>, SynthesisError> {
    let mut assembly = ProvingAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    {
        let circuit = EthereumBlockHeaderCircuit::<E>{
            num_headers: headers.len(),
            headers: Some(headers.clone()),
            engine: PhantomData,
        };
        circuit.synthesize(&mut assembly).expect("synthesize failed");
    }
    assembly.finalize();

    let proof = assembly.create_proof::<EthereumBlockHeaderCircuit<E>, T>(
        worker,
        setup,
        crs,
        transcript_params.clone()
    )?;

    let is_valid = verify::<_, _, T>(vk, &proof, transcript_params)?;
    assert!(is_valid);

    Ok(proof)
}
