mod affine_point_wrapper;
mod channel;
mod gadgets;
mod helper_functions;
mod utils;

use self::affine_point_wrapper::without_flag_unchecked::*;
use self::affine_point_wrapper::aux_data::*;
use self::affine_point_wrapper::*;
use self::channel::*;
use self::gadgets::*;
use self::helper_functions::*;
use self::utils::*;
use super::param::*;

use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::sha256::sha256 as sha256_circuit_hash;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::rescue::{RescueEngine, RescueHashParams, StatefulRescue};

use franklin_crypto::bellman::SynthesisError;

use franklin_crypto::plonk::circuit::bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::pairing::bn256::Bn256;
use franklin_crypto::bellman::plonk::better_better_cs::proof::{
    Proof,
};
use franklin_crypto::bellman::plonk::better_better_cs::setup::{
    VerificationKey, Setup,
};
use franklin_crypto::bellman::plonk::better_better_cs::verifier::{
    aggregate, verify,
};
use franklin_crypto::bellman::worker::Worker;

use franklin_crypto::plonk::circuit::Width4WithCustomGates;
use franklin_crypto::plonk::circuit::bigint::RnsParameters;

use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;

use franklin_crypto::bellman::pairing::{
    Engine,
    GenericCurveAffine,
};

use franklin_crypto::bellman::pairing::ff::{
    Field,
    PrimeField,
};
use franklin_crypto::bellman::plonk::domains::*;

use franklin_crypto::plonk::circuit::simple_term::*;

use super::gadgets::merkle::{MerkleGadget,MerkleDigest,RawMerkleDigest};
use super::gadgets::variable_keccak::{KeccakDigest,RawKeccakDigest};

#[derive(Clone)]
pub struct RawProofInputs<E: Engine> {
    pub parent_digest: RawKeccakDigest<E>,
    pub last_digest: RawKeccakDigest<E>,
    pub merkle_root: RawMerkleDigest<E>,
    pub for_gen: Option<Vec<E::Fr>>,
    pub for_x: Option<Vec<E::Fr>>,
}

impl<E:Engine> RawProofInputs<E> {
    fn parse(inputs: &[E::Fr]) -> Self {
        let (parent_digest, remaining) = RawKeccakDigest::<E>::parse_digest(inputs);
        let (last_digest, remaining) = RawKeccakDigest::<E>::parse_digest(remaining);
        let (merkle_root, remaining) = RawMerkleDigest::<E>::parse_digest(remaining);
        let (for_gen, remaining) = (remaining.get(0..8).map(|s| s.to_vec()), remaining.get(8..).unwrap_or(remaining));
        let for_x = remaining.get(0..8).map(|s| s.to_vec());
        Self { parent_digest, last_digest, merkle_root, for_gen, for_x }
    }
}

pub struct ProofInputs<E: Engine> {
    pub parent_digest: KeccakDigest<E>,
    pub last_digest: KeccakDigest<E>,
    pub merkle_root: MerkleDigest<E>,
    pub for_gen: Option<Vec<AllocatedNum<E>>>,
    pub for_x: Option<Vec<AllocatedNum<E>>>,
}

impl<E:Engine> ProofInputs<E> {
    pub const NUM_VARIABLES_INNER: usize = 2 * KeccakDigest::<E>::NUM_VARIABLES + MerkleDigest::<E>::NUM_VARIABLES;
    pub const NUM_VARIABLES_RECURSIVE: usize = Self::NUM_VARIABLES_INNER + 16;
    fn parse(inputs: &[AllocatedNum<E>]) -> Self {
        let (parent_digest, remaining) = KeccakDigest::<E>::parse_digest(inputs);
        let (last_digest, remaining) = KeccakDigest::<E>::parse_digest(remaining);
        let (merkle_root, remaining) = MerkleDigest::<E>::parse_digest(remaining);
        let (for_gen, remaining) = (remaining.get(0..8).map(|s| s.to_vec()), remaining.get(8..).unwrap_or(remaining));
        let for_x = remaining.get(0..8).map(|s| s.to_vec());
        Self { parent_digest, last_digest, merkle_root, for_gen, for_x }
    }
}

#[derive(Clone)]
pub struct RecursiveAggregationCircuit<
    'a,
    E: RescueEngine,
    C: Circuit<E>,
    OldP: PlonkConstraintSystemParams<E>,
    WP: WrappedAffinePoint<'a, E>,
    AD: AuxData<E>,
    T: ChannelGadget<E>,
> {
    pub num_proofs_to_check: usize,
    pub num_inputs: usize,
    pub inner_vk: &'a VerificationKey<E, C>,
    pub proofs: Option<&'a Vec<Proof<E, C>>>,
    pub rescue_params: &'a E::Params,
    pub rns_params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
    pub aux_data: AD,
    pub transcript_params: &'a T::Params,

    pub inputs: Option<Vec<RawProofInputs<E>>>,
    pub merkle_root: Option<RawMerkleDigest<E>>,

    pub is_inner_recursive: bool,
    pub is_outer_recursive: bool,

    pub g2_elements: Option<[E::G2Affine; 2]>,

    pub _m1: std::marker::PhantomData<WP>,
    pub _m2: std::marker::PhantomData<OldP>,
}
impl<
        'a,
        E: RescueEngine,
        C: Circuit<E>,
        OldP: PlonkConstraintSystemParams<E>,
        WP: WrappedAffinePoint<'a, E>,
        AD: AuxData<E>,
        T: ChannelGadget<E>,
    > Circuit<E> for RecursiveAggregationCircuit<'a, E, C, OldP, WP, AD, T>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    type MainGate = Width4MainGateWithDNext;

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(
            vec![
                Self::MainGate::default().into_internal(),
                TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
            ]
        )
    }

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        if let Some(proofs) = self.proofs.as_ref() {
            assert_eq!(self.num_proofs_to_check, proofs.len());
        }

        let mut proof_witnesses = vec![];
        let mut proof_inputs = Vec::with_capacity(self.num_proofs_to_check);
        let mut fs_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let proof_witness = self.proofs.as_ref().map(|el| &el[proof_index]);

            if let Some(proof) = proof_witness.as_ref() {
                assert_eq!(
                    proof.inputs.len(),
                    self.num_inputs,
                    "wrong number of inputs"
                );
            }

            let allocated_proof = ProofGadget::<E, WP>::alloc_from_witness::<_, _, OldP, _>(
                cs,
                self.num_inputs,
                proof_witness,
                self.rns_params,
                &self.aux_data,
                self.inner_vk.total_lookup_entries_length > 0,
            )?;

            let as_num_witness = allocated_proof.into_witness(cs)?;
            fs_witnesses.extend(as_num_witness);
            proof_inputs.push(ProofInputs::parse(&allocated_proof.input_values));
            proof_witnesses.push(allocated_proof);
        }

        let inner_vk = VerificationKeyGadget::<E, WP>::alloc::<CS, C, AD>(
            cs,
            self.inner_vk,
            self.rns_params,
            &self.aux_data,
        )?;


        let mut sponge = StatefulRescueGadget::<E>::new(self.rescue_params);

        for w in fs_witnesses.into_iter() {
            sponge.absorb_single_value(cs, w, self.rescue_params)?;
        }

        sponge.pad_if_necessary(self.rescue_params)?;

        let aggregation_challenge = sponge
            .squeeze_out_single(cs, self.rescue_params)?
            .into_allocated_num(cs)?;

        let mut pairs_for_generator = vec![];
        let mut pairs_for_x = vec![];

        for proof_idx in 0..self.num_proofs_to_check {
            let proof = &proof_witnesses[proof_idx];
            let inputs = &proof_inputs[proof_idx];

            let [pair_with_generator, pair_with_x] = aggregate_proof::<_, _, T, CS::Params, C, OldP, _, _>(
                cs,
                self.transcript_params,
                &inner_vk,
                &proof,
                &self.aux_data,
                self.rns_params,
            )?;

            pairs_for_generator.push(pair_with_generator);
            pairs_for_x.push(pair_with_x);

            // If inner circuit is recursive, aggregate the aggregated points from the inner circuit
            if self.is_inner_recursive {
                let limbs = [inputs.for_gen.as_ref().unwrap().as_slice(), inputs.for_x.as_ref().unwrap().as_slice()].concat();
                let (inner_pair_with_generator, rest) = WrappedAffinePoint::from_allocated_limb_witness(
                    cs, &limbs, &self.rns_params, &self.aux_data
                )?;
                let (inner_pair_with_x, rest) = WrappedAffinePoint::from_allocated_limb_witness(cs, rest, &self.rns_params, &self.aux_data)?;
                assert_eq!(rest.len(), 0);

                pairs_for_generator.push(inner_pair_with_generator);
                pairs_for_x.push(inner_pair_with_x);
            }

            if proof_idx > 0 {
                // check that parent hash == prev last hash
                proof_inputs[proof_idx].parent_digest.enforce_equal(
                    cs, &proof_inputs[proof_idx-1].last_digest
                )?;
            }
        }

        let mut scalars = vec![];
        scalars.push(aggregation_challenge.clone());

        let mut current = aggregation_challenge.clone();
        for _ in 1..pairs_for_generator.len() {
            let new = current.mul(cs, &aggregation_challenge)?;
            scalars.push(new.clone());

            current = new;
        }

        let pair_with_generator = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_generator,
            None,
            self.rns_params,
            &self.aux_data,
        )?;
        let pair_with_x = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_x,
            None,
            self.rns_params,
            &self.aux_data,
        )?;

        match (
            pair_with_generator.get_point().get_value(),
            pair_with_x.get_point().get_value(),
            self.g2_elements,
        ) {
            (Some(with_gen), Some(with_x), Some(g2_elements)) => {
                let valid = E::final_exponentiation(&E::miller_loop(&[
                    (&with_gen.prepare(), &g2_elements[0].prepare()),
                    (&with_x.prepare(), &g2_elements[1].prepare()),
                ]))
                .unwrap()
                    == E::Fqk::one();

                dbg!(valid);
            }
            _ => {}
        }

        let mut outputs = vec![];

        // verify first parent digest
        let parent_digest = KeccakDigest::alloc(cs, self.inputs.as_ref().map(|inps| inps[0].parent_digest))?;
        parent_digest.enforce_equal(cs, &proof_inputs[0].parent_digest)?;
        outputs.extend(&parent_digest.words);

        // verify last digest
        let last_digest = KeccakDigest::alloc(cs, self.inputs.as_ref().map(|inps| inps.last().unwrap().last_digest))?;
        last_digest.enforce_equal(cs, &proof_inputs.last().unwrap().last_digest)?;
        outputs.extend(&last_digest.words);

        // verify merkle tree root
        {
            let gadget = MerkleGadget::new(cs, false)?;
            let leaves = proof_inputs.iter().map(|inp| inp.merkle_root.into_le_bytes(cs)).collect::<Result<Vec<_>,_>>()?;
            let root = gadget.merkle_root(cs, leaves)?;

            let root_inp = MerkleDigest::alloc(cs, self.merkle_root)?;
            root.enforce_equal(cs, &root_inp)?;
            outputs.extend(&root_inp.words);
        }
        
        // add parameter for is outer recursive
        if self.is_outer_recursive {
            add_wp_points(&[pair_with_generator, pair_with_x], &mut outputs);
            for n in outputs.iter() {
                n.get_variable().inputize(cs)?;
            }
        } else {
            let mut hash_to_public_inputs = vec![];

            for n in outputs.iter() {
                hash_to_public_inputs.extend(allocated_num_to_aligned_big_endian(cs, &n.get_variable())?);
            }

            hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_generator)?);
            hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_x)?);

            let input_commitment = sha256_circuit_hash(cs, &hash_to_public_inputs)?;
            let keep = bytes_to_keep::<E>();
            assert!(keep <= 32);

            // we don't need to reverse again

            let mut lc = LinearCombination::<E>::zero();

            let mut coeff = E::Fr::one();

            for b in input_commitment[(32-keep)*8..].iter().rev() {
                lc.add_assign_boolean_with_coeff(b, coeff);
                coeff.double();
            }

            let as_num = lc.into_allocated_num(cs)?;
            as_num.inputize(cs)?;
        }

        Ok(())
    }
}

pub type RecursiveAggregationCircuitBn256<'a, C, P> = RecursiveAggregationCircuit::<'a, Bn256, C, P, WrapperUnchecked<'a, Bn256>, BN256AuxData, RescueChannelGadget<Bn256>>;

// TODO: these are ugly
fn fe_from_limbs<'a, E: RescueEngine>(limbs: &[E::Fr]) -> E::Fq {
    // TODO: fix hard-coded value
    const NBITS: u32 = 68;

    let mut repr = <E::Fq as PrimeField>::Repr::default();
    for (idx, x) in limbs.iter().enumerate() {
        let other_repr = x.into_repr();
        let mut other = <E::Fq as PrimeField>::Repr::default();
        assert!(NBITS < 128);
        other.as_mut()[0] = other_repr.as_ref()[0];
        other.as_mut()[1] = other_repr.as_ref()[1];
        other.shl(idx as u32 * NBITS);
        repr.add_nocarry(&other);
    }
    E::Fq::from_repr(repr).unwrap()
}

fn curve_from_limbs<'a, E: RescueEngine>(limbs: &[E::Fr]) -> Result<E::G1Affine, GroupDecodingError> {
    assert!(limbs.len() % 2 == 0);
    let x = fe_from_limbs::<E>(&limbs[0..limbs.len()/2]);
    let y = fe_from_limbs::<E>(&limbs[limbs.len()/2..]);
    <E::G1Affine as CurveAffine>::from_xy_checked(x, y)
}

fn make_aggregate<'a, E: RescueEngine, C: Circuit<E>, P: PlonkConstraintSystemParams<E>>(
    proofs: &[Proof<E, C>],
    inner_vk: &VerificationKey<E, C>,
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    is_inner_recursive: bool,
) -> Result<[E::G1Affine; 2], SynthesisError> {
    let mut channel = StatefulRescue::<E>::new(params);
    for p in proofs.iter() {
        let as_fe = <Proof<E, C> as IntoLimbedWitness<_, _, P>>::into_witness_for_params(p, rns_params)?;

        for fe in as_fe.into_iter() {
            channel.absorb_single_value(fe);
        }
    }

    channel.pad_if_necessary();

    let aggregation_challenge: E::Fr = channel.squeeze_out_single();

    let mut pair_with_generator = <E::G1 as CurveProjective>::zero();
    let mut pair_with_x = <E::G1 as CurveProjective>::zero();

    let mut current = aggregation_challenge;

    for proof in proofs.iter() {
        // FIXME we are duplicating some work here
        let ((for_gen, for_x), is_valid) = aggregate::<_, _, InnerTranscript<E>>(inner_vk, &proof, Some((params, rns_params))).expect("inner aggregate failed");
        assert!(is_valid, "individual proof is not valid");

        let is_valid = verify::<_, _, InnerTranscript<E>>(inner_vk, &proof, Some((params, rns_params))).expect("inner verify failed");
        assert!(is_valid, "individual proof is not valid");

        let contribution = <E::G1Affine as CurveAffine>::mul(&for_gen, current.into_repr());
        <E::G1 as CurveProjective>::add_assign(&mut pair_with_generator, &contribution);

        let contribution = <E::G1Affine as CurveAffine>::mul(&for_x, current.into_repr());
        <E::G1 as CurveProjective>::add_assign(&mut pair_with_x, &contribution);

        current.mul_assign(&aggregation_challenge);

        if is_inner_recursive {
            let inputs = RawProofInputs::<E>::parse(&proof.inputs);
            let inner_for_gen = curve_from_limbs::<E>(inputs.for_gen.unwrap().as_slice()).unwrap();
            let inner_for_x = curve_from_limbs::<E>(inputs.for_x.unwrap().as_slice()).unwrap();

            let contribution = <E::G1Affine as CurveAffine>::mul(&inner_for_gen, current.into_repr());
            <E::G1 as CurveProjective>::add_assign(&mut pair_with_generator, &contribution);
            let contribution = <E::G1Affine as CurveAffine>::mul(&inner_for_x, current.into_repr());
            <E::G1 as CurveProjective>::add_assign(&mut pair_with_x, &contribution);

            current.mul_assign(&aggregation_challenge);
        }
    }

    let pair_with_generator = <E::G1 as CurveProjective>::into_affine(&pair_with_generator);
    let pair_with_x = <E::G1 as CurveProjective>::into_affine(&pair_with_x);

    assert!(!<E::G1Affine as CurveAffine>::is_zero(&pair_with_generator));
    assert!(!<E::G1Affine as CurveAffine>::is_zero(&pair_with_x));

    Ok([pair_with_generator, pair_with_x])
}

fn make_public_input_and_limbed_aggregate<E: Engine, C: Circuit<E>>(
    proofs: &[Proof<E, C>],
    aggregate: &[E::G1Affine; 2],
    inputs: &Vec<E::Fr>,
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    is_inner_recursive: bool,
    is_outer_recursive: bool,
) -> (E::Fr, Vec<E::Fr>) {
    use std::io::Write;

    let (input, limbed_aggregate) = make_public_input_for_hashing_and_limbed_aggreagated(
        proofs,
        aggregate,
        inputs,
        rns_params,
        is_inner_recursive,
        is_outer_recursive
    );

    let mut hash_output = [0u8; 32];

    use sha2::{Sha256, Digest};
    let mut hasher = Sha256::new();
    hasher.update(&input);
    let result = hasher.finalize();

    (&mut hash_output[..]).write(&result.as_slice()).expect("must write");

    let keep = bytes_to_keep::<E>();
    for idx in 0..(32 - keep) {
        hash_output[idx] = 0;
    }

    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.read_be(&hash_output[..]).expect("must read BE repr");

    let fe = E::Fr::from_repr(repr).expect("must be valid representation");

    (fe, limbed_aggregate)
}

fn make_public_input_for_hashing_and_limbed_aggreagated<E: Engine, C: Circuit<E>>(
    _proofs: &[Proof<E, C>],
    aggregate: &[E::G1Affine; 2],
    inputs: &Vec<E::Fr>,
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    _is_inner_recursive: bool,
    _is_outer_recursive: bool,
) -> (Vec<u8>, Vec<E::Fr>) {
    let mut result = vec![];
    for input in inputs.iter() {
        add_field_element(input, &mut result);
    }

    add_point(&aggregate[0], &mut result, rns_params);
    add_point(&aggregate[1], &mut result, rns_params);

    let mut limbed_aggreagate = vec![];
    decompose_point_into_limbs(&aggregate[0], &mut limbed_aggreagate, rns_params);
    decompose_point_into_limbs(&aggregate[1], &mut limbed_aggreagate, rns_params);

    (result, limbed_aggreagate)
}

pub struct ProofCalldata<E: Engine> {
    pub num_proofs: u32,
    pub recursive_input_commitment: E::Fr,
    pub recursive_inputs: Vec<E::Fr>,
    pub proof: (Vec<E::Fq>, Vec<E::Fr>, Vec<E::Fq>),
    pub subproof_limbs: Vec<E::Fr>,
}

pub fn create_recursive_circuit_proof<'a, C: Circuit<Bn256>, OldP: PlonkConstraintSystemParams<Bn256>, T: Transcript<<Bn256 as ScalarEngine>::Fr>>(
    num_inputs: usize,
    proofs: &Vec<Proof<Bn256, C>>,
    inner_vk: &VerificationKey<Bn256, C>,
    recursive_circuit_vk: &VerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>, 
    recursive_circuit_setup: &Setup<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    quick_check_if_satisifed: bool,
    worker: &Worker,
    outer_transcript_params: Option<T::InitializationParameters>,
    is_inner_recursive: bool,
    is_outer_recursive: bool,
) -> Result<(Proof<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>, Option<ProofCalldata<Bn256>>), SynthesisError> {
    let rns_params = &*RNS_PARAMETERS;
    let inner_rescue_params = &INNER_RESCUE_PARAMETERS;

    let num_proofs_to_check = proofs.len();

    let aggregate = make_aggregate::<_, _, PlonkCsWidth4WithNextStepParams>(
        &proofs, 
        inner_vk,
        &inner_rescue_params,
        &rns_params,
        is_inner_recursive
    )?;

    println!("Assembling input to recursive circuit");

    let mut inputs: Vec<RawProofInputs<Bn256>> = Vec::with_capacity(num_inputs);
    for proof in proofs.iter() {
        inputs.push(RawProofInputs::parse(&proof.inputs));
    }
    let leaves: Vec<Vec<u8>> = inputs.iter().map(|inp| inp.merkle_root.to_bytes()).collect();
    let merkle_root = MerkleGadget::<Bn256>::raw_merkle_root(leaves);

    // compute cicuit inputs
    let actual_inputs: Vec<<Bn256 as ScalarEngine>::Fr> = [
        inputs[0].parent_digest.words.as_slice(),
        &inputs.last().unwrap().last_digest.words.as_slice(),
        &merkle_root.words.as_slice()
    ].concat();

    if is_outer_recursive {
        assert_eq!(recursive_circuit_setup.num_inputs, ProofInputs::<Bn256>::NUM_VARIABLES_RECURSIVE);
    } else {
        assert_eq!(recursive_circuit_setup.num_inputs, 1);
    }

    assert_eq!(recursive_circuit_vk.total_lookup_entries_length, 0);

    let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
    g2_bases.copy_from_slice(&crs.g2_monomial_bases.as_ref()[..]);

    let aux_data = BN256AuxData::new();

    let recursive_circuit_with_witness = RecursiveAggregationCircuitBn256::<C, OldP> {
        num_proofs_to_check,
        num_inputs,
        inner_vk,
        proofs: Some(proofs),
        rescue_params: &inner_rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &inner_rescue_params,
        
        inputs: Some(inputs),
        merkle_root: Some(merkle_root),
        is_inner_recursive,
        is_outer_recursive,

        g2_elements: Some(g2_bases),

        _m1: std::marker::PhantomData,
        _m2: std::marker::PhantomData,
    };

    if quick_check_if_satisifed {
        println!("Checking if satisfied");
        let mut assembly = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit_with_witness.synthesize(&mut assembly).expect("must synthesize");
        println!("Using {} gates for {} proofs aggregated", assembly.n(), num_proofs_to_check);
        let is_satisfied = assembly.is_satisfied();
        println!("Is satisfied = {}", is_satisfied);

        if is_satisfied == false {
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    let mut assembly = ProvingAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
    recursive_circuit_with_witness.synthesize(&mut assembly).expect("must synthesize");
    assembly.finalize();

    let proof = assembly.create_proof::<_, T>(
        &worker, 
        &recursive_circuit_setup, 
        &crs, 
        outer_transcript_params.clone()
    )?;

    let (expected_input, limbed_aggreagate) = make_public_input_and_limbed_aggregate(
        &proofs,
        &aggregate,
        &actual_inputs,
        &rns_params,
        is_inner_recursive,
        is_outer_recursive
    );
    
    if is_outer_recursive {
        let inputs = RawProofInputs::<Bn256>::parse(&proof.inputs);
        assert_eq!(inputs.for_gen.unwrap(), limbed_aggreagate[..8]);
        assert_eq!(inputs.for_x.unwrap(), limbed_aggreagate[8..]);
    } else {
        assert_eq!(proof.inputs.len(), 1);
        assert_eq!(proof.inputs[0], expected_input, "expected input is not equal to one in a circuit");
    }

    let is_valid = verify::<_, _, T>(
        &recursive_circuit_vk,
        &proof,
        outer_transcript_params
    )?;

    if is_valid == false {
        println!("Recursive circuit proof is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    let calldata = if is_outer_recursive {
        None
    } else {
        Some(ProofCalldata {
            num_proofs: proofs.len() as u32,
            recursive_input_commitment: proof.inputs[0],
            recursive_inputs: actual_inputs.clone(),
            proof: serialize_proof(&proof),
            subproof_limbs: limbed_aggreagate,
        })
    };

    Ok((proof, calldata))
}

fn serialize_proof<E: Engine, C: Circuit<E>>(proof: &Proof<E, C>) -> (Vec<E::Fq>, Vec<E::Fr>, Vec<E::Fq>) {
    let mut commitments = vec![];
    for p in proof.state_polys_commitments.iter()
        .chain(vec![&proof.copy_permutation_grand_product_commitment])
        .chain(proof.quotient_poly_parts_commitments.iter())
    {
        let (x, y) = CurveAffine::into_xy_unchecked(*p);
        commitments.push(x);
        commitments.push(y);
    }
    let mut openings = vec![];
    for fr in proof.state_polys_openings_at_z.iter()
        .chain(proof.state_polys_openings_at_dilations.iter().map(|x| &x.2))
        .chain(proof.gate_selectors_openings_at_z.iter().map(|x| &x.1))
        .chain(proof.copy_permutation_polys_openings_at_z.iter())
        .chain(vec![
            &proof.copy_permutation_grand_product_opening_at_z_omega,
            &proof.quotient_poly_opening_at_z,
            &proof.linearization_poly_opening_at_z,
        ])
    {
        openings.push(*fr);
    }
    let mut opening_proofs = vec![];
    for p in vec![&proof.opening_proof_at_z, &proof.opening_proof_at_z_omega]
    {
        let (x, y) = CurveAffine::into_xy_unchecked(*p);
        opening_proofs.push(x);
        opening_proofs.push(y);
    }
    (commitments, openings, opening_proofs)
}

pub fn create_recursive_circuit_setup<'a, C: Circuit<Bn256>, OldP: PlonkConstraintSystemParams<Bn256>>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    inner_vk: &VerificationKey<Bn256, C>,
    worker: &Worker,
    is_inner_recursive: bool,
    is_outer_recursive: bool,
) -> Result<Setup<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>, SynthesisError> {
    let mut assembly = SetupAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    let rns_params = &*RNS_PARAMETERS;
    let inner_rescue_params = &*INNER_RESCUE_PARAMETERS;
    let aux_data = BN256AuxData::new();

    let recursive_circuit = RecursiveAggregationCircuitBn256::<C, OldP> {
        num_proofs_to_check,
        num_inputs,
        inner_vk,
        proofs: None,
        rescue_params: &inner_rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &inner_rescue_params,

        inputs: None,
        merkle_root: None,
        is_inner_recursive,
        is_outer_recursive,

        g2_elements: None,

        _m1: std::marker::PhantomData,
        _m2: std::marker::PhantomData,
    };

    recursive_circuit.synthesize(&mut assembly)?;

    println!("Using {} gates", assembly.n());
    assembly.finalize();
    assembly.create_setup(&worker)
}

pub fn create_recursive_circuit_vk<'a, C: Circuit<Bn256>, OldP: PlonkConstraintSystemParams<Bn256>>(
    _num_proofs_to_check: usize,
    _num_inputs: usize,
    _inner_vk: &VerificationKey<Bn256, C>,
    setup: Setup<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    worker: &Worker,
) -> Result<VerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>, SynthesisError> 
{
    VerificationKey::<Bn256, RecursiveAggregationCircuitBn256<'a, C, OldP>>::from_setup(&setup, &worker, &crs)
}

#[track_caller]
pub fn aggregate_proof<'a, E, CS, T, P, C, OldP, AD, WP>(
    cs: &mut CS,
    channel_params: &'a T::Params,
    vk: &VerificationKeyGadget<'a, E, WP>,
    proof: &ProofGadget<'a, E, WP>,
    aux_data: &AD,
    params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
) -> Result<[WP; 2], SynthesisError>
    where 
    E: Engine, CS: ConstraintSystem<E>, T: ChannelGadget<E>, AD: AuxData<E>,
    P: PlonkConstraintSystemParams<E>, C: Circuit<E>, OldP: PlonkConstraintSystemParams<E>,
    WP: WrappedAffinePoint<'a, E>
{
    assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

    let mut channel = T::new(channel_params);

    if proof.num_inputs != vk.num_inputs {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let has_lookup = proof.has_lookup;
    let has_custom_gate = OldP::HAS_CUSTOM_GATES;
    if has_custom_gate {
        // We only support one type of custom gate: TwoBitDecompositionRangecheckCustomGate
        // XXX is there a better way to do this check?
        let declared_gates = C::declare_used_gates()?;
        assert_eq!(declared_gates.len(), 2);
        assert_eq!(declared_gates[0].name(), C::MainGate::default().name());
        assert_eq!(declared_gates[1].name(), <TwoBitDecompositionRangecheckCustomGate as GateInternal<E>>::name(&TwoBitDecompositionRangecheckCustomGate::default()));
    } else {
        // XXX is there a better way to do this check?
        let declared_gates = C::declare_used_gates()?;
        assert_eq!(declared_gates.len(), 1);
        assert_eq!(declared_gates[0].name(), C::MainGate::default().name());
    }

    let required_domain_size = if let Some(n) = vk.n {
        assert!(vk.domain_size_as_allocated_num.is_none());
        let required_domain_size = n + 1;
        if required_domain_size.is_power_of_two() == false {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        Some(required_domain_size)
    } else {
        assert!(vk.domain_size_as_allocated_num.is_some());

        None
    };

    let (omega_const, omega_inv_const) = if let Some(required_domain_size) = required_domain_size {
        let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;
        let omega = domain.generator;
        let omega_inv = domain.generator.inverse().expect("should exist");

        (Some(omega), Some(omega_inv))
    } else {
        (None, None)
    };

    let domain_size_decomposed = if let Some(domain_size) = vk.domain_size_as_allocated_num.as_ref() {
        assert!(vk.n.is_none());
        let absolute_limit = (E::Fr::S + 1) as usize;
        let decomposed = domain_size.into_bits_le(cs, Some(absolute_limit))?;

        Some(decomposed)
    } else {
        assert!(vk.n.is_some());

        None
    };

    let selector_d_next_index = P::STATE_WIDTH + 2;
    let selector_q_const_index = P::STATE_WIDTH + 1;
    let selector_q_m_index = P::STATE_WIDTH;

    // Commit public inputs
    for inp in proof.input_values.iter() {
        channel.consume(inp.clone(), cs)?;
    }

    // Commit wire values
    for w in proof.wire_commitments.iter() {
        channel.consume_point(cs, w.clone())?;
    }

    // XXX witness polys unimplemented

    let mut eta = None;
    if has_lookup {
        eta = Some(channel.produce_challenge(cs)?);

        channel.consume_point(cs, proof.lookup_s_poly_commitment.as_ref().unwrap().clone())?;
    }

    let beta = channel.produce_challenge(cs)?;
    let gamma = channel.produce_challenge(cs)?;

    // commit grand product
    channel.consume_point(cs, proof.copy_permutation_grand_product_commitment.clone())?;

    let mut beta_for_lookup = None;
    let mut gamma_for_lookup = None;
    if has_lookup {
        beta_for_lookup = Some(channel.produce_challenge(cs)?);
        gamma_for_lookup = Some(channel.produce_challenge(cs)?);

        channel.consume_point(cs, proof.lookup_grand_product_commitment.as_ref().unwrap().clone())?;
    }

    let alpha = channel.produce_challenge(cs)?;

    // Commit parts of the quotient polynomial
    for w in proof.quotient_poly_commitments.iter() {
        channel.consume_point(cs, w.clone())?;
    }

    let z = channel.produce_challenge(cs)?;
    channel.consume(proof.quotient_polynomial_at_z.clone(), cs)?;

    // commit every claimed value

    for el in proof.wire_values_at_z.iter() {
        channel.consume(el.clone(), cs)?;
    }

    for el in proof.wire_values_at_z_omega.iter() {
        channel.consume(el.clone(), cs)?;
    }

    if has_custom_gate {
        channel.consume(proof.gate_selector_values_at_z[0].clone(), cs)?;
    }

    for el in proof.permutation_polynomials_at_z.iter() {
        channel.consume(el.clone(), cs)?;
    }

    channel.consume(proof.copy_grand_product_at_z_omega.clone(), cs)?;

    if has_lookup {
        channel.consume(proof.lookup_t_poly_opening_at_z.as_ref().unwrap().clone(), cs)?;
        channel.consume(proof.lookup_selector_poly_opening_at_z.as_ref().unwrap().clone(), cs)?;
        channel.consume(proof.lookup_table_type_poly_opening_at_z.as_ref().unwrap().clone(), cs)?;
        
        channel.consume(proof.lookup_s_poly_opening_at_z_omega.as_ref().unwrap().clone(), cs)?;
        channel.consume(proof.lookup_grand_product_opening_at_z_omega.as_ref().unwrap().clone(), cs)?;
        channel.consume(proof.lookup_t_poly_opening_at_z_omega.as_ref().unwrap().clone(), cs)?;
    }

    channel.consume(proof.linearization_polynomial_at_z.clone(), cs)?;


    let z_in_pow_domain_size = if let Some(required_domain_size) = required_domain_size {
        assert!(required_domain_size.is_power_of_two());
        let mut z_in_pow_domain_size = z.clone();
        for _ in 0..required_domain_size.trailing_zeros() {
            z_in_pow_domain_size = z_in_pow_domain_size.square(cs)?;
        }

        z_in_pow_domain_size
    } else {
        let pow_decomposition = domain_size_decomposed.as_ref().unwrap();

        let mut pow_decomposition = pow_decomposition.to_vec();
        pow_decomposition.reverse();

        let z_in_pow_domain_size = AllocatedNum::<E>::pow(cs, &z, &pow_decomposition)?;

        z_in_pow_domain_size
    };

    let omega_inv_variable = if let Some(omega) = vk.omega_as_allocated_num.as_ref() {
        let inv = omega.inverse(cs).expect(&format!("Inverse of the domain generator must exist! Omega = {:?}", omega.get_value()));

        Some(inv)
    } else {
        None
    };

    let l_0_at_z = if let Some(required_domain_size) = required_domain_size { 
        let omega_inv = omega_inv_const.unwrap();
        let l_0_at_z = evaluate_lagrange_poly(
            cs, 
            required_domain_size, 
            0, 
            &omega_inv, 
            z.clone(), 
            z_in_pow_domain_size.clone()
        )?;

        l_0_at_z
    } else {
        let l_0_at_z = evaluate_lagrange_poly_for_variable_domain_size(
            cs,
            0,
            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
            omega_inv_variable.as_ref().unwrap(),
            z.clone(), 
            z_in_pow_domain_size.clone()
        )?;

        l_0_at_z
    };

    let l_minus1_at_z = if let Some(required_domain_size) = required_domain_size {
        let omega_inv = omega_inv_const.unwrap();
        let l_minus1_at_z = evaluate_lagrange_poly(
            cs, 
            required_domain_size, 
            required_domain_size - 1, 
            &omega_inv, 
            z.clone(), 
            z_in_pow_domain_size.clone()
        )?;

        l_minus1_at_z
    } else {
        unimplemented!();
    };

    let mut lookup_beta_plus_1 = None;
    let mut lookup_gamma_beta = None;
    if has_lookup {
        lookup_beta_plus_1 = Some(beta_for_lookup.unwrap().add_constant(cs, E::Fr::one())?);
        lookup_gamma_beta = Some(lookup_beta_plus_1.unwrap().mul(cs, &gamma_for_lookup.unwrap())?);
    }

    let z_minus_omega_inv = z.sub_constant(cs, omega_inv_const.unwrap())?;
    
    let alpha_pow_2 = alpha.mul(cs, &alpha)?;
    let alpha_pow_3 = alpha_pow_2.mul(cs, &alpha)?;
    let alpha_pow_4 = alpha_pow_3.mul(cs, &alpha)?;
    let alpha_pow_5 = alpha_pow_4.mul(cs, &alpha)?;
    let alpha_pow_6 = alpha_pow_5.mul(cs, &alpha)?;

    // do the actual check for relationship at z
    {
        let mut lhs = proof.quotient_polynomial_at_z.clone();
        let vanishing_at_z = evaluate_vanishing_poly(cs, z_in_pow_domain_size.clone())?;
        lhs = lhs.mul(cs, &vanishing_at_z)?;

        let mut rhs = proof.linearization_polynomial_at_z.clone();

        // add public inputs
        {
            let mut inputs_term = AllocatedNum::zero(cs);
            for (idx, input) in proof.input_values.iter().enumerate() {
                let tmp = if idx == 0 {
                    l_0_at_z.mul(cs, &input)?
                } else {
                    let tmp = if let Some(required_domain_size) = required_domain_size { 
                        let omega_inv = omega_inv_const.unwrap();
                        let tmp = evaluate_lagrange_poly(cs, required_domain_size, idx, &omega_inv, z.clone(), z_in_pow_domain_size.clone())?;

                        tmp
                    } else {
                        let tmp = evaluate_lagrange_poly_for_variable_domain_size(
                            cs,
                            idx,
                            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
                            omega_inv_variable.as_ref().unwrap(),
                            z.clone(), 
                            z_in_pow_domain_size.clone()
                        )?;

                        tmp
                    };

                    tmp.mul(cs, &input)?
                }; 
                inputs_term = inputs_term.add(cs, &tmp)?;
            }
            if has_custom_gate {
                inputs_term = inputs_term.mul(cs, &proof.gate_selector_values_at_z[0])?;
            }
            rhs = rhs.add(cs, &inputs_term)?;
        }

        // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

        let mut z_part = proof.copy_grand_product_at_z_omega.clone();

        for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
            let mut tmp = p.clone();
            tmp = tmp.mul(cs, &beta)?;
            tmp = tmp.add(cs, &gamma)?;
            tmp = tmp.add(cs, &w)?;

            z_part = z_part.mul(cs, &tmp)?;
        }   

        // last poly value and gamma
        let mut tmp = gamma.clone();
        tmp = tmp.add(cs, &proof.wire_values_at_z.iter().rev().next().unwrap())?;

        z_part = z_part.mul(cs, &tmp)?;
        
        z_part = if has_custom_gate {
            z_part.mul(cs, &alpha_pow_5)?
        } else {
            z_part.mul(cs, &alpha)?
        };

        rhs = rhs.sub(cs, &z_part)?; 

        // - L_0(z) * \alpha^2
        let tmp = if has_custom_gate {
            l_0_at_z.mul(cs, &alpha_pow_6)?
        } else {
            l_0_at_z.mul(cs, &alpha_pow_2)?
        };
        rhs = rhs.sub(cs, &tmp)?;

        if has_lookup {
            let expected = AllocatedNum::pow(cs, &lookup_gamma_beta.unwrap(), decompose_const_to_bits::<E, _>(&[(required_domain_size.unwrap() - 1) as u64]))?;

            let mut tmp = proof.lookup_s_poly_opening_at_z_omega.unwrap().mul(cs, &beta_for_lookup.unwrap())?;
            tmp = tmp.add(cs, &lookup_gamma_beta.unwrap())?;
            tmp = tmp.mul(cs, &proof.lookup_grand_product_opening_at_z_omega.unwrap())?;
            tmp = tmp.mul(cs, &alpha_pow_3)?;
            tmp = tmp.mul(cs, &z_minus_omega_inv)?;
            rhs = rhs.add(cs, &tmp)?;

            let tmp = l_0_at_z.mul(cs, &alpha_pow_4)?;
            rhs = rhs.sub(cs, &tmp)?;

            let mut tmp = l_minus1_at_z.mul(cs, &expected)?;
            tmp = tmp.mul(cs, &alpha_pow_5)?;
            rhs = rhs.sub(cs, &tmp)?;
        }

        lhs.enforce_equal(cs, &rhs)?;
    }

    let v = channel.produce_challenge(cs)?;

    channel.consume_point(cs, proof.opening_at_z_proof.clone())?;
    channel.consume_point(cs, proof.opening_at_z_omega_proof.clone())?;

    let u = channel.produce_challenge(cs)?;

    // first let's reconstruct the linearization polynomial from
    // honomorphic commitments, and simultaneously add (through the separation scalar "u")
    // part for opening of z(X) at z*omega

    let mut virtual_commitment_for_linearization_poly = {
        let mut points: Vec<WP> = vec![];
        let mut scalars: Vec<AllocatedNum<E>> = vec![];
        
        points.push(vk.gate_setup_commitments[selector_q_const_index].clone());
        if has_custom_gate {
            scalars.push(proof.gate_selector_values_at_z[0].clone());
        } else {
            scalars.push(AllocatedNum::one(cs));
        }

        // main gate. Does NOT include public inputs
        {
            // Q_const(x)
            for i in 0..P::STATE_WIDTH {
                // Q_k(X) * K(z)
                // here multiexp may be used
                points.push(vk.gate_setup_commitments[i].clone());
                let scalar = if has_custom_gate {
                    proof.gate_selector_values_at_z[0].mul(cs, &proof.wire_values_at_z[i])?
                } else {
                    proof.wire_values_at_z[i].clone()
                };
                scalars.push(scalar);
            }

            // Q_m(X) * A(z) * B(z)
            // add to multiexp as well
            let mut scalar = proof.wire_values_at_z[0].clone();
            scalar = scalar.mul(cs, &proof.wire_values_at_z[1])?;
            if has_custom_gate {
                scalar = scalar.mul(cs, &proof.gate_selector_values_at_z[0])?;
            }
            points.push(vk.gate_setup_commitments[selector_q_m_index].clone());
            scalars.push(scalar);

            points.push(vk.gate_setup_commitments[selector_d_next_index].clone());
            let scalar = if has_custom_gate {
                proof.gate_selector_values_at_z[0].mul(cs, &proof.wire_values_at_z_omega[0])?
            } else {
                proof.wire_values_at_z_omega[0].clone()
            };
            scalars.push(scalar);
        }

        // add contribution from range constraint gate
        if has_custom_gate {
            let mut scalar;
            let one_fr = AllocatedNum::alloc(cs, || {
                Ok(E::Fr::one())
            })?;
            let two_fr = AllocatedNum::alloc(cs, || {
                let mut fr = E::Fr::one();
                fr.add_assign(&E::Fr::one());
                Ok(fr)
            })?;
            let three_fr = AllocatedNum::alloc(cs, || {
                let mut fr = E::Fr::one();
                fr.add_assign(&E::Fr::one());
                fr.add_assign(&E::Fr::one());
                Ok(fr)
            })?;
            let four_fr = AllocatedNum::alloc(cs, || {
                let mut fr = E::Fr::one();
                fr.add_assign(&E::Fr::one());
                fr.add_assign(&E::Fr::one());
                fr.add_assign(&E::Fr::one());
                Ok(fr)
            })?;
            scalar = AllocatedNum::zero(cs);

            let mut current_alpha = alpha;
            for i in 0..4 {
                let tmp = proof.wire_values_at_z[3 - i].mul(cs, &four_fr)?;
                let t1 = if i == 3 {
                    proof.wire_values_at_z_omega[0].sub(cs, &tmp)?
                } else {
                    proof.wire_values_at_z[2 - i].sub(cs, &tmp)?
                };

                let tmp = t1.sub(cs, &one_fr)?;
                let mut t2 = t1.mul(cs, &tmp)?; 

                let tmp = t1.sub(cs, &two_fr)?;
                t2 = t2.mul(cs, &tmp)?;

                let tmp = t1.sub(cs, &three_fr)?;
                t2 = t2.mul(cs, &tmp)?;

                t2 = t2.mul(cs, &current_alpha)?;
                scalar = scalar.add(cs, &t2)?;

                current_alpha = current_alpha.mul(cs, &alpha)?;
            }
            points.push(vk.gate_selector_commitments[1].clone());
            scalars.push(scalar);  
        }     

        // v * [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() * z(X) -
        // - \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X) +
        // + alpha^2 * L_0(z) * z(X) ] + 
        // + v^{P} * u * z(X)
        // and join alpha^2 * L_0(z) and v^{P} * u into the first term containing z(X)

        // [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() + alpha^2 * L_0(z)] * z(X)
        let grand_product_part_at_z = {
            let mut scalar: Option<AllocatedNum<E>> = None;

            // permutation part
            for (_i, (wire, non_res)) in proof.wire_values_at_z.iter()
                            .zip(Some(E::Fr::one()).iter().chain(&vk.copy_permutation_non_residues)).enumerate() 
            {
                // tmp = non_res * z * beta + wire
                use franklin_crypto::plonk::circuit::Assignment;

                let mut tmp = AllocatedNum::alloc(
                    cs,
                    || {
                        // non_res * z * beta + wire

                        let mut result = *z.get_value().get()?;
                        result.mul_assign(beta.get_value().get()?);
                        result.mul_assign(&non_res);

                        result.add_assign(wire.get_value().get()?);

                        Ok(result)
                    }
                )?;

                // create arithmetic terms

                let z_beta_by_non_res_term = ArithmeticTerm::from_variable_and_coeff(z.get_variable(), *non_res).mul_by_variable(beta.get_variable());
                let wire_term = ArithmeticTerm::from_variable(wire.get_variable());
                let tmp_term = ArithmeticTerm::from_variable(tmp.get_variable());
                let mut term = MainGateTerm::new();
                term.add_assign(z_beta_by_non_res_term);
                term.add_assign(wire_term);
                term.sub_assign(tmp_term);

                cs.allocate_main_gate(term)?;

                // we've enforces tmp value

                // let mut tmp = AllocatedNum::general_equation(cs, &z, &beta, &wire, non_res, &zero, &zero, &one, &zero)?;

                // on first iteration: scalar = tmp + gamma
                // else: scalar = scalar * (tmp + gamma)

                if let Some(existing_scalar) = scalar.take() {
                    tmp = tmp.add(cs, &gamma)?;
                    let s = existing_scalar.mul(cs, &tmp)?;

                    scalar = Some(s);
                } else {
                    let s = tmp.add(cs, &gamma)?;

                    scalar = Some(s);
                } 

                assert!(scalar.is_some());
            }

            let mut scalar = scalar.unwrap();

            scalar = if has_custom_gate {
                scalar.mul(cs, &alpha_pow_5)?
            } else {
                scalar.mul(cs, &alpha)?
            };

            // + L_0(z) * alpha^2
            let tmp = if has_custom_gate {
                l_0_at_z.mul(cs, &alpha_pow_6)?
            } else {
                l_0_at_z.mul(cs, &alpha_pow_2)?
            };

            scalar.add(cs, &tmp)?
        };

        // \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X)
        let last_permutation_part_at_z = {
            let mut scalar: Option<AllocatedNum<E>> = None;

            // permutation part
            for (_i, (wire, perm_at_z)) in proof.wire_values_at_z.iter()
                            .zip(&proof.permutation_polynomials_at_z).enumerate() 
            {
                // tmp = perm_at_z * beta + wire
                use franklin_crypto::plonk::circuit::Assignment;

                let mut tmp = AllocatedNum::alloc(
                    cs,
                    || {
                        // perm(z) * beta + wire

                        let mut result = *beta.get_value().get()?;
                        result.mul_assign(perm_at_z.get_value().get()?);

                        result.add_assign(wire.get_value().get()?);

                        Ok(result)
                    }
                )?;

                // create arithmetic terms

                let z_beta_by_non_res_term = ArithmeticTerm::from_variable(perm_at_z.get_variable()).mul_by_variable(beta.get_variable());
                let wire_term = ArithmeticTerm::from_variable(wire.get_variable());
                let tmp_term = ArithmeticTerm::from_variable(tmp.get_variable());
                let mut term = MainGateTerm::new();
                term.add_assign(z_beta_by_non_res_term);
                term.add_assign(wire_term);
                term.sub_assign(tmp_term);

                cs.allocate_main_gate(term)?;

                // tmp is now constrained

                // on first iteration: scalar = tmp + gamma
                // else: scalar = scalar * (tmp + gamma)

                if let Some(existing_scalar) = scalar.take() {
                    tmp = tmp.add(cs, &gamma)?;
                    let s = existing_scalar.mul(cs, &tmp)?;

                    scalar = Some(s);
                } else {
                    let s = tmp.add(cs, &gamma)?;
                    
                    scalar = Some(s);
                }

                assert!(scalar.is_some());
            }

            let mut scalar = scalar.unwrap();

            scalar = scalar.mul(cs, &beta)?.mul(cs, &proof.copy_grand_product_at_z_omega)?;
            scalar = if has_custom_gate {
                scalar.mul(cs, &alpha_pow_5)?
            } else {
                scalar.mul(cs, &alpha)?
            };

            scalar
        };

        {
            // also add to multiexp
            points.push(proof.copy_permutation_grand_product_commitment.clone());
            scalars.push(grand_product_part_at_z);
            
            let mut last_permutation = vk.copy_permutation_commitments.last().unwrap().clone();
            points.push(last_permutation.negate(cs, params)?);
            scalars.push(last_permutation_part_at_z);
        }

        if has_lookup {
            let mut current_alpha = if has_custom_gate {
                alpha_pow_6.clone()
            } else {
                alpha_pow_2.clone()
            };
            current_alpha = current_alpha.mul(cs, &alpha)?;
            let mut factor = proof.lookup_grand_product_opening_at_z_omega.unwrap().mul(cs, &current_alpha)?;
            factor = factor.mul(cs, &z_minus_omega_inv)?;
            points.push(proof.lookup_s_poly_commitment.as_ref().unwrap().clone());
            scalars.push(factor);

            let mut factor = proof.lookup_t_poly_opening_at_z_omega.unwrap().mul(cs, &beta_for_lookup.unwrap())?;
            factor = factor.add(cs, &proof.lookup_t_poly_opening_at_z.unwrap())?;
            factor = factor.add(cs, &lookup_gamma_beta.unwrap())?;
            
            let mut current = eta.unwrap();
            let mut f_reconstructed = proof.wire_values_at_z[0];
            for i in 1..(P::STATE_WIDTH - 1) {
                let tmp = proof.wire_values_at_z[i].mul(cs, &current)?;
                f_reconstructed = f_reconstructed.add(cs, &tmp)?;
                current = current.mul(cs, &eta.unwrap())?;
            }
            let tmp = proof.lookup_table_type_poly_opening_at_z.as_ref().unwrap().mul(cs, &current)?;
            f_reconstructed = f_reconstructed.add(cs, &tmp)?;
            f_reconstructed = f_reconstructed.mul(cs, &proof.lookup_selector_poly_opening_at_z.as_ref().unwrap())?;
            f_reconstructed = f_reconstructed.add(cs, &gamma_for_lookup.unwrap())?;
            factor = factor.mul(cs, &f_reconstructed)?;
            
            factor = factor.mul(cs, &lookup_beta_plus_1.unwrap())?;
            //factor = factor.negate(cs)?;
            factor = AllocatedNum::zero(cs).sub(cs, &factor)?;
            factor = factor.mul(cs, &current_alpha)?;
            factor = factor.mul(cs, &z_minus_omega_inv)?;
            
            current_alpha = current_alpha.mul(cs, &alpha)?;
            let tmp = l_0_at_z.mul(cs, &current_alpha)?;
            factor = factor.add(cs, &tmp)?;
            
            current_alpha = current_alpha.mul(cs, &alpha)?;
            let tmp = l_minus1_at_z.mul(cs, &current_alpha)?;
            factor = factor.add(cs, &tmp)?;
            points.push(proof.lookup_grand_product_commitment.as_ref().unwrap().clone());
            scalars.push(factor);
        }

        let mut r = WP::multiexp(cs, &scalars[..], &points[..], None, params, aux_data)?;

        r = r.mul(cs, &v, None, params, aux_data)?;

        r
    };

    // now check the openings
    // aggregate t(X) from parts

    let mut commitments_aggregation = proof.quotient_poly_commitments[0].clone();

    let mut scalars : Vec<AllocatedNum<E>> = vec![];
    let mut points: Vec<WP> = vec![];

    let mut current = z_in_pow_domain_size.clone();
    for part in proof.quotient_poly_commitments.iter().skip(1) {
        //second multiexp
        points.push(part.clone());
        scalars.push(current.clone());
        current = current.mul(cs, &z_in_pow_domain_size)?;
    }

    let mut multiopening_challenge = v.clone();
    // power of v is contained inside
    commitments_aggregation = commitments_aggregation.add(cs, &mut virtual_commitment_for_linearization_poly, params)?;

    // do the same for wires
    for com in proof.wire_commitments.iter() {
        // add to second multiexp as well
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        points.push(com.clone());
        scalars.push(multiopening_challenge.clone());
    }

    // gate selectors
    if has_custom_gate {
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        points.push(vk.gate_selector_commitments[0].clone());
        scalars.push(multiopening_challenge.clone());
    }

    // and for all permutation polynomials except the last one
    assert_eq!(vk.copy_permutation_commitments.len(), proof.permutation_polynomials_at_z.len() + 1);
    
    let arr_len = vk.copy_permutation_commitments.len();
    for com in vk.copy_permutation_commitments[0..(arr_len - 1)].iter() {
        // v^{1+STATE_WIDTH + STATE_WIDTH - 1}
        // second multiexp
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        points.push(com.clone());
        scalars.push(multiopening_challenge.clone());
    }

    // lookup commitments at z
    if has_lookup {
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?;

        let mut commitments_iter = vk.lookup_tables_commitments.iter();
        points.push(commitments_iter.next().unwrap().clone());
        scalars.push(multiopening_challenge.clone());

        let mut current = eta.unwrap().clone();
        for part in commitments_iter {
            points.push(part.clone());
            let tmp = multiopening_challenge.mul(cs, &current)?;
            scalars.push(tmp);
            current = current.mul(cs, &eta.unwrap())?;
        }

        multiopening_challenge = multiopening_challenge.mul(cs, &v)?;
        points.push(vk.lookup_selector_commitment.as_ref().unwrap().clone());
        scalars.push(multiopening_challenge.clone());
        
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?;
        points.push(vk.lookup_table_type_commitment.as_ref().unwrap().clone());
        scalars.push(multiopening_challenge.clone());
    }
    
    // we skip z(X) at z
    multiopening_challenge = multiopening_challenge.mul(cs, &v)?;
    let scalar = multiopening_challenge.mul(cs, &u)?;
    points.push(proof.copy_permutation_grand_product_commitment.clone());
    scalars.push(scalar);

    // aggregate last wire commitment (that is opened at z*omega)
    // using multiopening challenge and u
    multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
    let scalar = multiopening_challenge.mul(cs, &u)?;
    // add to second multiexp
    points.push(proof.wire_commitments.last().unwrap().clone());
    scalars.push(scalar);

    // lookup for z*omega
    if has_lookup {
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        let scalar = multiopening_challenge.mul(cs, &u)?;
        points.push(proof.lookup_s_poly_commitment.as_ref().unwrap().clone());
        scalars.push(scalar.clone());
        
        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        let scalar = multiopening_challenge.mul(cs, &u)?;
        points.push(proof.lookup_grand_product_commitment.as_ref().unwrap().clone());
        scalars.push(scalar.clone());

        multiopening_challenge = multiopening_challenge.mul(cs, &v)?; 
        let scalar = multiopening_challenge.mul(cs, &u)?;
        let mut commitments_iter = vk.lookup_tables_commitments.iter();
        points.push(commitments_iter.next().unwrap().clone());
        scalars.push(scalar.clone());

        let mut current = eta.unwrap().clone();
        for part in commitments_iter {
            points.push(part.clone());
            let tmp = scalar.mul(cs, &current)?;
            scalars.push(tmp);
            current = current.mul(cs, &eta.unwrap())?;
        }
    }

    // subtract the opening value using one multiplication
    let lookup_values_queried_at_z = if has_lookup {
        vec![
            proof.lookup_t_poly_opening_at_z.as_ref().unwrap(),
            proof.lookup_selector_poly_opening_at_z.as_ref().unwrap(),
            proof.lookup_table_type_poly_opening_at_z.as_ref().unwrap(),
        ]
    } else {
        vec![]
    };

    let mut multiopening_challenge_for_values = v.clone();
    let mut aggregated_value = proof.quotient_polynomial_at_z.clone();
    for (i, value_at_z) in Some(proof.linearization_polynomial_at_z.clone()).iter()
            .chain(&proof.wire_values_at_z)
            .chain(&proof.gate_selector_values_at_z)
            .chain(&proof.permutation_polynomials_at_z)
            .chain(lookup_values_queried_at_z)
            .enumerate() 
    {
        if i != 0 { 
            multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
        };
        
        let tmp = value_at_z.mul(cs, &multiopening_challenge_for_values)?;
        aggregated_value = aggregated_value.add(cs, &tmp)?;
    }

    // add parts that are opened at z*omega using `u`
    multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
    let tmp = proof.copy_grand_product_at_z_omega.mul(cs, &multiopening_challenge_for_values)?;
    let mut aggregated_value_at_z_omega = tmp;

    {
        multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
        let tmp = proof.wire_values_at_z_omega[0].mul(cs, &multiopening_challenge_for_values)?;
        aggregated_value_at_z_omega = aggregated_value_at_z_omega.add(cs, &tmp)?;
    }

    // lookup at z*omega
    if has_lookup {
        multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
        let tmp = proof.lookup_s_poly_opening_at_z_omega.as_ref().unwrap().mul(cs, &multiopening_challenge_for_values)?;
        aggregated_value_at_z_omega = aggregated_value_at_z_omega.add(cs, &tmp)?;

        multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
        let tmp = proof.lookup_grand_product_opening_at_z_omega.as_ref().unwrap().mul(cs, &multiopening_challenge_for_values)?;
        aggregated_value_at_z_omega = aggregated_value_at_z_omega.add(cs, &tmp)?;
        
        multiopening_challenge_for_values = multiopening_challenge_for_values.mul(cs, &v)?;
        let tmp = proof.lookup_t_poly_opening_at_z_omega.as_ref().unwrap().mul(cs, &multiopening_challenge_for_values)?;
        aggregated_value_at_z_omega = aggregated_value_at_z_omega.add(cs, &tmp)?;
    }

    aggregated_value_at_z_omega = aggregated_value_at_z_omega.mul(cs, &u)?;
    aggregated_value = aggregated_value.add(cs, &aggregated_value_at_z_omega)?;

    // make equivalent of (f(x) - f(z))
    // also add to second multiexp
    let mut val = <E::G1Affine as CurveAffine>::one();
    <E::G1Affine as CurveAffine>::negate(&mut val);
    points.push(WP::constant(val, params));
    scalars.push(aggregated_value);

    // next, we need to check that
    // e(proof_for_z + u*proof_for_z_omega, g2^x) = 
    // e(z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening), g2^1) 
    // however, we are going to compute the pairing itself outside the circuit
    // here we only go to prepare the pairing argumets:
    // arg1 = proof_for_z + u*proof_for_z_omega
    // arg2 = z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening)

    let mut opening_at_z_proof = proof.opening_at_z_proof.clone();
    let mut opening_at_z_omega_proof = proof.opening_at_z_omega_proof.clone();
    let mut pair_with_x_negated = opening_at_z_omega_proof.mul(cs, &u, None, params, aux_data)?;
    pair_with_x_negated = pair_with_x_negated.add(cs, &mut opening_at_z_proof, params)?;
    
    let pair_with_x = pair_with_x_negated.negate(cs, params)?;

    // to second multiexp
    points.push(proof.opening_at_z_proof.clone());
    scalars.push(z.clone());

    let z_omega_term = if let Some(_required_domain_size) = required_domain_size { 
        let omega = omega_const.unwrap();
        
        let mut z_omega_term = Term::<E>::from_allocated_num(z.clone());
        z_omega_term.scale(&omega);

        z_omega_term
    } else {
        let omega = vk.omega_as_allocated_num.as_ref().unwrap().clone();

        let omega_term = Term::<E>::from_allocated_num(omega);
        let z_term = Term::<E>::from_allocated_num(z.clone());

        let z_omega_term = z_term.mul(cs, &omega_term)?;

        z_omega_term
    };

    let u_as_term = Term::<E>::from_allocated_num(u.clone());
    // z*omega*u
    let z_omega_by_u = z_omega_term.mul(cs, &u_as_term)?.collapse_into_num(cs)?.get_variable();

    points.push(proof.opening_at_z_omega_proof.clone());
    scalars.push(z_omega_by_u);

    let mut tmp = WP::multiexp(cs, &scalars[..], &points[..], None, params, aux_data)?;
    //to second multiexp
    let pair_with_generator = commitments_aggregation.add(cs, &mut tmp, params)?;

    Ok([pair_with_generator, pair_with_x])
}

pub trait IntoLimbedWitness<E: Engine, C: Circuit<E>, P: PlonkConstraintSystemParams<E>> {
    fn into_witness(&self) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn witness_size_for_params(_params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> usize {
        unimplemented!()
    }
    fn into_witness_for_params(&self, _params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base >) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
}

impl<E: Engine, C: Circuit<E>, P: PlonkConstraintSystemParams<E>> IntoLimbedWitness<E, C, P> for Proof<E, C> {
    fn into_witness_for_params(&self, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Result<Vec<E::Fr>, SynthesisError> {
        let as_limbs = proof_into_single_limb_witness(&self, params);
        Ok(as_limbs)
    }
}

pub trait IntoLimbedCircuitWitness<E: Engine> {
    fn into_witness<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        unimplemented!()
    }
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> IntoLimbedCircuitWitness<E> for ProofGadget<'a, E, WP> {
    fn into_witness<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = vec![];

        add_scalar_field_elements(&self.input_values, &mut result);
        add_wp_points(&self.wire_commitments, &mut result);
        add_wp_points(&[self.copy_permutation_grand_product_commitment.clone()], &mut result);
        if self.has_lookup {
            add_wp_points(&[self.lookup_s_poly_commitment.as_ref().unwrap().clone()], &mut result);
            add_wp_points(&[self.lookup_grand_product_commitment.as_ref().unwrap().clone()], &mut result);
        }
        add_wp_points(&self.quotient_poly_commitments, &mut result);

        add_scalar_field_elements(&self.wire_values_at_z, &mut result);
        add_scalar_field_elements(&self.wire_values_at_z_omega, &mut result);
        add_scalar_field_elements(&self.gate_selector_values_at_z, &mut result);

        add_scalar_field_elements(&[self.copy_grand_product_at_z_omega.clone()], &mut result);
        if self.has_lookup {
            add_scalar_field_elements(&[self.lookup_s_poly_opening_at_z_omega.as_ref().unwrap().clone()], &mut result);
            add_scalar_field_elements(&[self.lookup_grand_product_opening_at_z_omega.as_ref().unwrap().clone()], &mut result);
            add_scalar_field_elements(&[self.lookup_t_poly_opening_at_z.as_ref().unwrap().clone()], &mut result);
            add_scalar_field_elements(&[self.lookup_t_poly_opening_at_z_omega.as_ref().unwrap().clone()], &mut result);
            add_scalar_field_elements(&[self.lookup_selector_poly_opening_at_z.as_ref().unwrap().clone()], &mut result);
            add_scalar_field_elements(&[self.lookup_table_type_poly_opening_at_z.as_ref().unwrap().clone()], &mut result);
        }
        add_scalar_field_elements(&[self.quotient_polynomial_at_z.clone()], &mut result);
        add_scalar_field_elements(&[self.linearization_polynomial_at_z.clone()], &mut result);
        add_scalar_field_elements(&self.permutation_polynomials_at_z, &mut result);

        add_wp_points(&[self.opening_at_z_proof.clone(), self.opening_at_z_omega_proof.clone()], &mut result);

        Ok(result)
    }
}

pub fn proof_into_allocated_limb_witnesses<E: Engine, C: Circuit<E>>(
    proof: &Proof<E, C>,
    params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Vec<E::Fr> 
{
    let has_lookup = proof.lookup_s_poly_commitment.is_some();
    let mut encodings = vec![];

    encodings.extend_from_slice(&proof.inputs);

    for x in proof.state_polys_commitments.iter() {
        add_ff_point(x, &mut encodings, params);
    }

    assert_eq!(proof.witness_polys_commitments.len(), 0);

    add_ff_point(&proof.copy_permutation_grand_product_commitment, &mut encodings, params);

    if has_lookup {
        add_ff_point(&proof.lookup_s_poly_commitment.unwrap(), &mut encodings, params);
        add_ff_point(&proof.lookup_grand_product_commitment.unwrap(), &mut encodings, params);
    }

    for x in proof.quotient_poly_parts_commitments.iter() {
        add_ff_point(x, &mut encodings, params);
    }

    encodings.extend_from_slice(&proof.state_polys_openings_at_z);
    for (_, _, x) in proof.state_polys_openings_at_dilations.iter() {
        encodings.push(*x);
    }
    
    assert_eq!(proof.gate_setup_openings_at_z.len(), 0);

    for (_, x) in proof.gate_selectors_openings_at_z.iter() {
        encodings.push(*x);
    }

    encodings.push(proof.copy_permutation_grand_product_opening_at_z_omega);
    if has_lookup {
        encodings.push(proof.lookup_s_poly_opening_at_z_omega.unwrap());
        encodings.push(proof.lookup_grand_product_opening_at_z_omega.unwrap());
        encodings.push(proof.lookup_t_poly_opening_at_z.unwrap());
        encodings.push(proof.lookup_t_poly_opening_at_z_omega.unwrap());
        encodings.push(proof.lookup_selector_poly_opening_at_z.unwrap());
        encodings.push(proof.lookup_table_type_poly_opening_at_z.unwrap());
    }
    encodings.push(proof.quotient_poly_opening_at_z);
    encodings.push(proof.linearization_poly_opening_at_z);
    encodings.extend_from_slice(&proof.copy_permutation_polys_openings_at_z);

    add_ff_point(&proof.opening_proof_at_z, &mut encodings, params);
    add_ff_point(&proof.opening_proof_at_z_omega, &mut encodings, params);

    encodings
}

pub fn proof_into_single_limb_witness<E: Engine, C: Circuit<E>>(
    proof: &Proof<E, C>,
    params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) -> Vec<E::Fr> 
{
    // change the params
    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);

    let params = &new_params;

    // encode
    proof_into_allocated_limb_witnesses(proof, params)
}
