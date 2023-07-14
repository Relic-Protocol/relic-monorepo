use franklin_crypto::jive::JiveEngine;
use franklin_crypto::jive::bn256::Bn256JiveParams;
use franklin_crypto::plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;

use franklin_crypto::bellman::{SynthesisError, ScalarEngine};
use franklin_crypto::bellman::bn256::Bn256;
use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof;
use franklin_crypto::bellman::plonk::better_better_cs::setup::{VerificationKey, Setup};
use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
use franklin_crypto::plonk::circuit::allocated_num::Num;
use franklin_crypto::bellman::worker::Worker;
use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;

use super::gadgets::header::parse_header;
use super::gadgets::merkle::MerkleGadget;
use super::gadgets::sha256::{Sha256Hasher, Sha256Digest};
use super::gadgets::utils::num::NumExtension;
use super::gadgets::utils::rlc::JiveRLCGadget;
use super::gadgets::variable_jive::{JiveGadget, JiveDigest};
use super::gadgets::variable_keccak::{RawKeccakDigest, KeccakDigest};
use super::gadgets::header::{BlockHeaderHasher, BlockHeaderVec};

#[derive(Debug)]
pub struct EthereumBlockHeaderCircuit<E: JiveEngine>{
    jive_params: E::Params,
    num_headers: usize,
    headers: Option<Vec<Vec<u8>>>,
}

impl<E: JiveEngine> EthereumBlockHeaderCircuit<E> {
    pub const NUM_INPUTS: usize = 2 * KeccakDigest::<E>::NUM_VARIABLES + Sha256Digest::<E>::NUM_VARIABLES + JiveDigest::<E>::NUM_VARIABLES;
}

impl<E: JiveEngine> Circuit<E> for EthereumBlockHeaderCircuit<E> {
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
        inscribe_combined_bitwise_ops_and_range_table(cs, 8).unwrap();

        if let Some(headers) = &self.headers {
            assert_eq!(self.num_headers, headers.len());
        }

        let hasher: BlockHeaderHasher<E> = BlockHeaderHasher::new(cs)?;
        let jive_gadget = JiveGadget::new(&self.jive_params);
        let mut rlc = JiveRLCGadget::new(&self.jive_params);
        let mut hashes = Vec::with_capacity(self.num_headers);
        let mut hashes_raw = self.headers.as_ref().map(|_| Vec::with_capacity(self.num_headers));
        let mut parent_hashes = Vec::with_capacity(self.num_headers);
        let mut parent_hashes_raw = self.headers.as_ref().map(|_| Vec::with_capacity(self.num_headers));
        let mut header_roots = Vec::with_capacity(self.num_headers);

        for idx in 0..self.num_headers {
            let header = self.headers.as_ref().map(|headers| headers[idx].clone());
            if let Some(header) = &header {
                // compute raw block hash
                hashes_raw.as_mut().unwrap().push(BlockHeaderHasher::<E>::raw_digest(&header));

                // pull out parent hash from header
                // parent hash starts 4 bytes into the header
                let parent_hash = RawKeccakDigest::from_bytes::<32>(header[4..36].try_into().unwrap());
                parent_hashes_raw.as_mut().unwrap().push(parent_hash);
            }

            let header_bytes = BlockHeaderVec::alloc(cs, header)?;
            hashes.push(hasher.digest(cs, &header_bytes)?);

            // parent hash is the first RLP element in the block header
            // at byte offset 4, so we'll compare 32bit chunks
            let parent_digest_words = header_bytes.vals()[4..36]
                .chunks(8)
                .map(|chunk| Num::from_le_bytes(cs, chunk))
                .collect::<Result<Vec<_>,_>>()?;
            parent_hashes.push(KeccakDigest::parse_digest_nums(parent_digest_words.as_slice()).0);

            let parsed = parse_header(cs, &mut rlc, &header_bytes)?;
            header_roots.push(parsed.merkle_root(cs, &jive_gadget)?);
        }

        // finalize the RLC constraints from parsing the headers
        rlc.finalize(cs)?;

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


        // compute and inputize merkle tree root
        {
            let hasher = Sha256Hasher::new(cs, true)?;
            let merkle_gadget = MerkleGadget::new(&hasher);
            let root = merkle_gadget.merkle_root(cs, hashes)?;
            root.inputize(cs)?;
        }

        // compute and inputize auxiliary root
        {
            let merkle_gadget = MerkleGadget::new(&jive_gadget);
            let root = merkle_gadget.merkle_root(cs, header_roots)?;
            root.inputize(cs)?;
        }

        Ok(())
    }
}

pub fn create_inner_circuit_setup(
    worker: &Worker,
    num_headers: usize
) -> Result<Setup<Bn256, EthereumBlockHeaderCircuit<Bn256>>, SynthesisError> {
    let circuit = EthereumBlockHeaderCircuit{
        jive_params: Bn256JiveParams::new(false),
        num_headers,
        headers: None
    };
    let mut assembly = SetupAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
    circuit.synthesize(&mut assembly)?;
    println!("Using {} gates", assembly.n());
    assembly.finalize();
    println!("Using {} gates (final)", assembly.n());
    assembly.create_setup(worker)
}

pub fn create_inner_circuit_vk(
    worker: &Worker,
    setup: Setup<Bn256, EthereumBlockHeaderCircuit<Bn256>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
) -> Result<VerificationKey<Bn256, EthereumBlockHeaderCircuit<Bn256>>, SynthesisError> {
    VerificationKey::<Bn256, EthereumBlockHeaderCircuit<Bn256>>::from_setup(&setup, worker, crs)
}

pub fn create_inner_circuit_proof<T: Transcript<<Bn256 as ScalarEngine>::Fr>>(
    worker: &Worker,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    vk: &VerificationKey<Bn256, EthereumBlockHeaderCircuit<Bn256>>,
    setup: &Setup<Bn256, EthereumBlockHeaderCircuit<Bn256>>,
    transcript_params: Option<T::InitializationParameters>,
    headers: &Vec<Vec<u8>>,
) -> Result<Proof<Bn256, EthereumBlockHeaderCircuit<Bn256>>, SynthesisError> {
    let mut assembly = ProvingAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

    {
        let circuit = EthereumBlockHeaderCircuit::<Bn256>{
            jive_params: Bn256JiveParams::new(false),
            num_headers: headers.len(),
            headers: Some(headers.clone())
        };
        circuit.synthesize(&mut assembly).expect("synthesize failed");
    }
    assembly.finalize();

    let proof = assembly.create_proof::<EthereumBlockHeaderCircuit<Bn256>, T>(
        worker,
        setup,
        crs,
        transcript_params.clone()
    )?;

    let is_valid = verify::<_, _, T>(vk, &proof, transcript_params)?;
    assert!(is_valid);

    Ok(proof)
}
