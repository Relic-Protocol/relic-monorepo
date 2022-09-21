use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::plonk::cs::gates::*;
use crate::plonk::cs::*;

use crate::worker::*;
use super::polynomials::*;
use super::domains::*;
use crate::plonk::commitments::*;
use crate::plonk::commitments::transcript::*;
use crate::plonk::utils::*;
use crate::plonk::generator::*;
use crate::plonk::prover::*;

fn evaluate_inverse_vanishing_poly<E: Engine>(vahisning_size: usize, point: E::Fr) -> E::Fr {
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

    let domain = Domain::<E::Fr>::new_for_size(vahisning_size as u64).expect("should fit");
    let n_domain_omega = domain.generator;
    let root = n_domain_omega.pow([(vahisning_size - 1) as u64]);

    let mut numerator = point;
    numerator.sub_assign(&root);

    let mut denominator = point.pow([vahisning_size as u64]);
    denominator.sub_assign(&E::Fr::one());

    let denominator = denominator.inverse().expect("must exist");

    numerator.mul_assign(&denominator);

    numerator
}

fn evaluate_lagrange_poly<E: Engine>(vahisning_size:usize, poly_number: usize, at: E::Fr) -> E::Fr {
    assert!(vahisning_size.is_power_of_two());

    let mut repr = E::Fr::zero().into_repr();
    repr.as_mut()[0] = vahisning_size as u64;

    let size_fe = E::Fr::from_repr(repr).expect("is a valid representation");
    // let size_inv = n_fe.inverse().expect("must exist");

    // L_0(X) = (Z_H(X) / (X - 1)).(1/n) and L_0(1) = 1
    // L_1(omega) = 1 = L_0(omega * omega^-1)

    let domain = Domain::<E::Fr>::new_for_size(vahisning_size as u64).expect("domain of this size should exist");
    let omega = domain.generator;

    let omega_inv = omega.inverse().expect("must exist");

    let argument_multiplier = omega_inv.pow([poly_number as u64]);
    let mut argument = at;
    argument.mul_assign(&argument_multiplier);

    let mut numerator = argument.pow([vahisning_size as u64]);
    numerator.sub_assign(&E::Fr::one());

    let mut denom = argument;
    denom.sub_assign(&E::Fr::one());
    denom.mul_assign(&size_fe);

    let denom_inv = denom.inverse().expect("must exist");

    numerator.mul_assign(&denom_inv);

    numerator
}

pub fn verify_nonhomomorphic<E: Engine, S: CommitmentScheme<E::Fr, Prng = T>, T: Transcript<E::Fr, Input = S::Commitment>>(
    setup: &PlonkSetup<E, S>,
    proof: &PlonkNonhomomorphicProof<E, S>, 
    meta: S::Meta,
    large_meta: S::Meta
) -> Result<bool, SynthesisError> {
    assert!(S::IS_HOMOMORPHIC == false);

    let num_gates = setup.n;

    let committer = S::new_for_size(num_gates.next_power_of_two(), meta);
    let large_committer = S::new_for_size(4 * num_gates.next_power_of_two(), large_meta);

    let mut transcript = T::new();

    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = setup.n + 1;
    assert!(required_domain_size.is_power_of_two());

    transcript.commit_input(&proof.a_commitment);
    transcript.commit_input(&proof.b_commitment);
    transcript.commit_input(&proof.c_commitment);

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    transcript.commit_input(&proof.z_1_commitment);
    transcript.commit_input(&proof.z_2_commitment);

    // we do not commit those cause those are known already

    let n_fe = E::Fr::from_str(&setup.n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    let alpha = transcript.get_challenge();

    transcript.commit_input(&proof.t_commitment);

    let z = transcript.get_challenge();

    // this is a sanity check

    let a_at_z = proof.a_opening_value;
    let b_at_z = proof.b_opening_value;
    let c_at_z = proof.c_opening_value;

    let q_l_at_z = proof.q_l_opening_value;
    let q_r_at_z = proof.q_r_opening_value;
    let q_o_at_z = proof.q_o_opening_value;
    let q_m_at_z = proof.q_m_opening_value;
    let q_c_at_z = proof.q_c_opening_value;

    let s_id_at_z = proof.s_id_opening_value;
    let sigma_1_at_z = proof.sigma_1_opening_value;
    let sigma_2_at_z = proof.sigma_2_opening_value;
    let sigma_3_at_z = proof.sigma_3_opening_value;

    let mut inverse_vanishing_at_z = evaluate_inverse_vanishing_poly::<E>(required_domain_size.next_power_of_two(), z);

    let z_1_at_z = proof.z_1_unshifted_opening_value;
    let z_2_at_z = proof.z_2_unshifted_opening_value;

    let z_1_shifted_at_z = proof.z_1_shifted_opening_value;
    let z_2_shifted_at_z = proof.z_2_shifted_opening_value;

    let l_0_at_z = evaluate_lagrange_poly::<E>(required_domain_size.next_power_of_two(), 0, z);
    let l_n_minus_one_at_z = evaluate_lagrange_poly::<E>(required_domain_size.next_power_of_two(), setup.n - 1, z);

    let t_at_z = proof.t_opening_value;

    {
        transcript.commit_field_element(&a_at_z);
        transcript.commit_field_element(&b_at_z);
        transcript.commit_field_element(&c_at_z);

        transcript.commit_field_element(&q_l_at_z);
        transcript.commit_field_element(&q_r_at_z);
        transcript.commit_field_element(&q_o_at_z);
        transcript.commit_field_element(&q_m_at_z);
        transcript.commit_field_element(&q_c_at_z);

        transcript.commit_field_element(&s_id_at_z);
        transcript.commit_field_element(&sigma_1_at_z);
        transcript.commit_field_element(&sigma_2_at_z);
        transcript.commit_field_element(&sigma_3_at_z);

        transcript.commit_field_element(&t_at_z);

        transcript.commit_field_element(&z_1_at_z);
        transcript.commit_field_element(&z_2_at_z);

        transcript.commit_field_element(&z_1_shifted_at_z);
        transcript.commit_field_element(&z_2_shifted_at_z);
    }

    let aggregation_challenge = transcript.get_challenge();

    // let shifted_opening_aggregation_challenge = transcript.get_challenge();

    // TODO: add public inputs

    // verify by blindly assembling a t poly
    let mut t_1 = {
        let mut res = q_c_at_z;

        let mut tmp = q_l_at_z;
        tmp.mul_assign(&a_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_r_at_z;
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_o_at_z;
        tmp.mul_assign(&c_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_m_at_z;
        tmp.mul_assign(&a_at_z);
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        res
    };

    {
        let mut res = z_1_at_z;

        let mut tmp = s_id_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&two_n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_1_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_2_at_z;

        let mut tmp = sigma_1_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_2_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_3_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_2_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_shifted_at_z;
        res.sub_assign(&z_2_shifted_at_z);
        res.mul_assign(&l_n_minus_one_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_at_z;
        res.sub_assign(&z_2_at_z);
        res.mul_assign(&l_0_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;

    let mut z_by_omega = z;
    z_by_omega.mul_assign(&domain.generator);

    let commitments = vec![
        &proof.a_commitment,
        &proof.b_commitment,
        &proof.c_commitment,
        &setup.q_l,
        &setup.q_r,
        &setup.q_o,
        &setup.q_m,
        &setup.q_c,
        &setup.s_id,
        &setup.sigma_1,
        &setup.sigma_2,
        &setup.sigma_3,
        &proof.z_1_commitment,
        &proof.z_2_commitment,
        &proof.z_1_commitment,
        &proof.z_2_commitment,
    ];

    let claimed_values = vec![
        a_at_z,
        b_at_z,
        c_at_z,
        q_l_at_z,
        q_r_at_z,
        q_o_at_z,
        q_m_at_z,
        q_c_at_z,
        s_id_at_z,
        sigma_1_at_z,
        sigma_2_at_z,
        sigma_3_at_z,
        z_1_at_z,
        z_2_at_z,
        z_1_shifted_at_z,
        z_2_shifted_at_z,
    ];

    let opening_points = vec![
        z, 
        z,
        z,

        z, 
        z,
        z,
        z,
        z,

        z,
        z,
        z,
        z,

        z,
        z,

        z_by_omega,
        z_by_omega
    ];

    if t_1 != t_at_z {
        println!("Recalculated t(z) is not equal to the provided value");
        return Ok(false);
    }

    let valid = committer.verify_multiple_openings(commitments, opening_points, &claimed_values, aggregation_challenge, &proof.openings_proof, &mut transcript);

    if !valid {
        println!("Multiopening is invalid");
        return Ok(false);
    }

    let valid = large_committer.verify_single(&proof.t_commitment, z, proof.t_opening_value, &proof.t_opening_proof, &mut transcript);

    if !valid {
        println!("T commitment opening is invalid");
        return Ok(false);
    }



    // let mut opening_point = z;
    // opening_point.mul_assign(&domain.generator);

    // let commitments = vec![
    //     &proof.z_1_commitment,
    //     &proof.z_2_commitment,
    // ];

    // let claimed_values = vec![
    //     proof.z_1_shifted_opening_value,
    //     proof.z_2_shifted_opening_value
    // ];

    // let valid = committer.verify_multiple_openings(commitments, opening_point, &claimed_values, shifted_opening_aggregation_challenge, &proof.shifted_openings_proof, &mut transcript);

    Ok(valid)
}

pub fn verify_nonhomomorphic_chunked<E: Engine, S: CommitmentScheme<E::Fr, Prng = T>, T: Transcript<E::Fr, Input = S::Commitment>>(
    setup: &PlonkSetup<E, S>,
    proof: &PlonkChunkedNonhomomorphicProof<E, S>, 
    meta: S::Meta
) -> Result<bool, SynthesisError> {
    assert!(S::IS_HOMOMORPHIC == false);

    let num_gates = setup.n;

    let committer = S::new_for_size(num_gates.next_power_of_two(), meta);

    let mut transcript = T::new();

    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = setup.n + 1;
    assert!(required_domain_size.is_power_of_two());

    transcript.commit_input(&proof.a_commitment);
    transcript.commit_input(&proof.b_commitment);
    transcript.commit_input(&proof.c_commitment);

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    transcript.commit_input(&proof.z_1_commitment);
    transcript.commit_input(&proof.z_2_commitment);

    // we do not commit those cause those are known already

    let n_fe = E::Fr::from_str(&setup.n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    let alpha = transcript.get_challenge();

    transcript.commit_input(&proof.t_low_commitment);
    transcript.commit_input(&proof.t_mid_commitment);
    transcript.commit_input(&proof.t_high_commitment);

    let z = transcript.get_challenge();

    // this is a sanity check

    let a_at_z = proof.a_opening_value;
    let b_at_z = proof.b_opening_value;
    let c_at_z = proof.c_opening_value;

    let q_l_at_z = proof.q_l_opening_value;
    let q_r_at_z = proof.q_r_opening_value;
    let q_o_at_z = proof.q_o_opening_value;
    let q_m_at_z = proof.q_m_opening_value;
    let q_c_at_z = proof.q_c_opening_value;

    let s_id_at_z = proof.s_id_opening_value;
    let sigma_1_at_z = proof.sigma_1_opening_value;
    let sigma_2_at_z = proof.sigma_2_opening_value;
    let sigma_3_at_z = proof.sigma_3_opening_value;

    let mut inverse_vanishing_at_z = evaluate_inverse_vanishing_poly::<E>(required_domain_size, z);

    let z_1_at_z = proof.z_1_unshifted_opening_value;
    let z_2_at_z = proof.z_2_unshifted_opening_value;

    let z_1_shifted_at_z = proof.z_1_shifted_opening_value;
    let z_2_shifted_at_z = proof.z_2_shifted_opening_value;

    let l_0_at_z = evaluate_lagrange_poly::<E>(required_domain_size, 0, z);
    let l_n_minus_one_at_z = evaluate_lagrange_poly::<E>(required_domain_size, setup.n - 1, z);

    let t_low_at_z = proof.t_low_opening_value;
    let t_mid_at_z = proof.t_mid_opening_value;
    let t_high_at_z = proof.t_high_opening_value;

    let z_in_pow_of_domain_size = z.pow([required_domain_size as u64]);

    let mut t_at_z = E::Fr::zero();
    t_at_z.add_assign(&t_low_at_z);

    let mut tmp = z_in_pow_of_domain_size;
    tmp.mul_assign(&t_mid_at_z);
    t_at_z.add_assign(&tmp);

    let mut tmp = z_in_pow_of_domain_size;
    tmp.mul_assign(&z_in_pow_of_domain_size);
    tmp.mul_assign(&t_high_at_z);
    t_at_z.add_assign(&tmp);

    {
        transcript.commit_field_element(&a_at_z);
        transcript.commit_field_element(&b_at_z);
        transcript.commit_field_element(&c_at_z);

        transcript.commit_field_element(&q_l_at_z);
        transcript.commit_field_element(&q_r_at_z);
        transcript.commit_field_element(&q_o_at_z);
        transcript.commit_field_element(&q_m_at_z);
        transcript.commit_field_element(&q_c_at_z);

        transcript.commit_field_element(&s_id_at_z);
        transcript.commit_field_element(&sigma_1_at_z);
        transcript.commit_field_element(&sigma_2_at_z);
        transcript.commit_field_element(&sigma_3_at_z);

        transcript.commit_field_element(&t_low_at_z);
        transcript.commit_field_element(&t_mid_at_z);
        transcript.commit_field_element(&t_high_at_z);

        transcript.commit_field_element(&z_1_at_z);
        transcript.commit_field_element(&z_2_at_z);

        transcript.commit_field_element(&z_1_shifted_at_z);
        transcript.commit_field_element(&z_2_shifted_at_z);
    }

    let aggregation_challenge = transcript.get_challenge();

    // TODO: add public inputs

    // verify by blindly assembling a t poly
    let mut t_1 = {
        let mut res = q_c_at_z;

        let mut tmp = q_l_at_z;
        tmp.mul_assign(&a_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_r_at_z;
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_o_at_z;
        tmp.mul_assign(&c_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_m_at_z;
        tmp.mul_assign(&a_at_z);
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        res
    };

    {
        let mut res = z_1_at_z;

        let mut tmp = s_id_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&two_n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_1_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_2_at_z;

        let mut tmp = sigma_1_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_2_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_3_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_2_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_shifted_at_z;
        res.sub_assign(&z_2_shifted_at_z);
        res.mul_assign(&l_n_minus_one_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_at_z;
        res.sub_assign(&z_2_at_z);
        res.mul_assign(&l_0_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;

    let mut z_by_omega = z;
    z_by_omega.mul_assign(&domain.generator);

    let commitments = vec![
        &proof.a_commitment,
        &proof.b_commitment,
        &proof.c_commitment,
        &setup.q_l,
        &setup.q_r,
        &setup.q_o,
        &setup.q_m,
        &setup.q_c,
        &setup.s_id,
        &setup.sigma_1,
        &setup.sigma_2,
        &setup.sigma_3,
        &proof.z_1_commitment,
        &proof.z_2_commitment,
        &proof.z_1_commitment,
        &proof.z_2_commitment,
        &proof.t_low_commitment,
        &proof.t_mid_commitment,
        &proof.t_high_commitment,
    ];

    let claimed_values = vec![
        a_at_z,
        b_at_z,
        c_at_z,
        q_l_at_z,
        q_r_at_z,
        q_o_at_z,
        q_m_at_z,
        q_c_at_z,
        s_id_at_z,
        sigma_1_at_z,
        sigma_2_at_z,
        sigma_3_at_z,
        z_1_at_z,
        z_2_at_z,
        z_1_shifted_at_z,
        z_2_shifted_at_z,
        t_low_at_z,
        t_mid_at_z,
        t_high_at_z,
    ];

    let opening_points = vec![
        z, 
        z,
        z,

        z, 
        z,
        z,
        z,
        z,

        z,
        z,
        z,
        z,

        z,
        z,

        z_by_omega,
        z_by_omega,

        z,
        z,
        z,
    ];

    if t_1 != t_at_z {
        println!("Recalculated t(z) is not equal to the provided value");
        return Ok(false);
    }

    let valid = committer.verify_multiple_openings(commitments, opening_points, &claimed_values, aggregation_challenge, &proof.openings_proof, &mut transcript);

    if !valid {
        println!("Multiopening is invalid");
        return Ok(false);
    }

    Ok(valid)
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine};

    use crate::{SynthesisError};
    use std::marker::PhantomData;

    use crate::plonk::cs::gates::*;
    use crate::plonk::cs::*;

    struct TestCircuit<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            cs.enforce_zero_2((a, b), (two, negative_one))?;

            let ten = E::Fr::from_str("10").unwrap();
            cs.enforce_zero_2((b, c), (ten, negative_one))?;

            cs.enforce_mul_3((a, b, c))?;

            Ok(())
        }
    }

    struct InvalidTestCircuit<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for InvalidTestCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("11").unwrap())
            })?;

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            cs.enforce_zero_2((a, b), (two, negative_one))?;

            let ten = E::Fr::from_str("10").unwrap();
            cs.enforce_zero_2((b, c), (ten, negative_one))?;

            cs.enforce_mul_3((a, b, c))?;

            Ok(())
        }
    }

    #[test]
    fn test_small_circuit_transparent_verification() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let circuit = TestCircuit::<Bn256> {
            _marker: PhantomData
        };

        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta).unwrap();

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        println!("Proving");

        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();


        println!("Verifying");

        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();

        assert!(valid);
    }

    #[test]
    fn test_small_circuit_invalid_witness_transparent_verification() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let circuit = InvalidTestCircuit::<Bn256> {
            _marker: PhantomData
        };

        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta.clone()).unwrap();

        println!("Proving");

        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();

        println!("Verifying");

        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();

        assert!(!valid);
    }

    #[derive(Clone)]
    struct BenchmarkCircuit<E:Engine>{
        num_steps: usize,
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();

            let mut two = one;
            two.double();
            
            let mut a = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            let mut b = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            cs.enforce_zero_2((a, CS::ONE), (one, negative_one))?;
            cs.enforce_zero_2((b, CS::ONE), (one, negative_one))?;

            let mut c = cs.alloc(|| {
                Ok(two)
            })?;

            cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;

            let mut a_value = one;
            let mut b_value = one;
            let mut c_value = two;

            for _ in 0..self.num_steps {
                a = b;
                b = c;

                a_value = b_value;
                b_value = c_value;
                c_value.add_assign(&a_value);

                c = cs.alloc(|| {
                    Ok(c_value)
                })?;

                cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bench_fibonacci_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Bn256> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Bn256>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    // #[test]
    // fn test_bench_keccak_for_fibonacci_circuit() {
    //     use crate::pairing::bn256::{Bn256, Fr};
    //     use crate::plonk::utils::*;
    //     use crate::plonk::commitments::transparent::fri::*;
    //     use crate::plonk::commitments::transparent::iop::*;
    //     use crate::plonk::commitments::transcript::*;
    //     use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
    //     use crate::plonk::commitments::transparent::iop::keccak_trivial_iop::*;
    //     use crate::plonk::commitments::*;
    //     use crate::plonk::commitments::transparent::*;

    //     use std::time::Instant;

    //     type Iop = TrivialKeccakIOP<Fr>;
    //     type Fri = NaiveFriIop<Fr, Iop>;
    //     type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

    //     let meta = TransparentCommitterParameters {
    //         lde_factor: 16,
    //         num_queries: 10,
    //         output_coeffs_at_degree_plus_one: 16,
    //     };

    //     let meta_large = TransparentCommitterParameters {
    //         lde_factor: 16,
    //         num_queries: 10,
    //         output_coeffs_at_degree_plus_one: 16,
    //     };

    //     let circuit = BenchmarkCircuit::<Bn256> {
    //         num_steps: 1_000_000,
    //         _marker: PhantomData
    //     };

    //     println!("Start setup");
    //     let start = Instant::now();
    //     let setup = setup::<Bn256, Committer, _>(&circuit, meta).unwrap();
    //     println!("Setup taken {:?}", start.elapsed());

    //     println!("Using circuit with N = {}", setup.n);

    //     let meta = TransparentCommitterParameters {
    //         lde_factor: 16,
    //         num_queries: 10,
    //         output_coeffs_at_degree_plus_one: 16,
    //     };

    //     println!("Start proving");
    //     let start = Instant::now();
    //     let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, meta, meta_large).unwrap();
    //     println!("Proof taken {:?}", start.elapsed());

    //     let meta = TransparentCommitterParameters {
    //         lde_factor: 16,
    //         num_queries: 10,
    //         output_coeffs_at_degree_plus_one: 16,
    //     };

    //     let meta_large = TransparentCommitterParameters {
    //         lde_factor: 16,
    //         num_queries: 10,
    //         output_coeffs_at_degree_plus_one: 16,
    //     };

    //     println!("Start verifying");
    //     let start = Instant::now();
    //     let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();
    //     println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

    //     assert!(!valid);
    // }

    #[test]
    fn test_bench_homomorphic_plonk() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Bn256;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::worker::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        const SAMPLES: usize = 1 << 20;
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
        let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

        println!("Done generating test points and scalars");

        let pool = Worker::new();
        let start = std::time::Instant::now();

        let _sparse = multiexp(
            &pool,
            (Arc::new(g), 0),
            FullDensity,
            Arc::new(v)
        ).wait().unwrap();

        let per_one_poly = start.elapsed().as_micros();
        // a, b, c, z_1, z_2, t, opening at z (of length t), opening at z*omega(of length a)
        let total_expected_plonk = per_one_poly * (5 + 1 + 3 + 3 + 1); 
        println!("{} ms for expected plonk with ~ {} gates", total_expected_plonk/1000u128, SAMPLES);
    }

    #[test]
    fn test_bench_transparent_engine() {
        use crate::plonk::transparent_engine::proth_engine::*;
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let mut negative_one = Fr::one();
        negative_one.negate();
        println!("-1 = {}", negative_one);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Transparent252> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Transparent252>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    #[test]
    fn test_bench_chunked_proof_on_transparent_engine() {
        use crate::plonk::transparent_engine::proth_engine::*;
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let mut negative_one = Fr::one();
        negative_one.negate();
        println!("-1 = {}", negative_one);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Transparent252> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Transparent252>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta.clone()).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &aux, meta.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    #[test]
    fn test_poly_eval_correctness() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::worker::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000];

        let x: Fr = rng.gen();

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let mut point = Fr::one();
            let mut result = Fr::zero();
            for c in coeffs.iter() {
                let mut tmp = point;
                tmp.mul_assign(&c);
                result.add_assign(&tmp);

                point.mul_assign(&x);
            }

            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let eval_result = poly.evaluate_at(&worker, x);
            assert!(eval_result == result, "failed for size {}", poly_size);
        }
    }

    #[test]
    fn test_poly_grand_product_correctness() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::worker::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).filter(|el| !el.is_zero()).collect::<Vec<_>>();
            let poly = Polynomial::<Fr, _>::from_values_unpadded(coeffs).unwrap();
            let palallel_result = poly.calculate_grand_product(&worker).unwrap();
            let serial_result = poly.calculate_grand_product_serial().unwrap();

            if palallel_result != serial_result {
                for (i, (c0, c1)) in palallel_result.as_ref().iter()
                                .zip(serial_result.as_ref().iter())
                                .enumerate() 
                {
                    assert!(c0 == c1, "failed at value number {} for size {}", i, poly_size);
                }
            }
        }
    }

    #[test]
    fn test_bench_lde() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use std::time::Instant;
        use crate::worker::*;
        use crate::plonk::commitments::transparent::utils::*;

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000, 2_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
        
            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let start = Instant::now();
            let _eval_result = poly.lde(&worker, 16);
            println!("LDE with factor 16 for size {} taken {:?}", poly_size, start.elapsed());

            let coeffs = (0..(16*poly_size)).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
        
            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let start = Instant::now();
            let eval_result = poly.clone().fft(&worker);
            println!("FFT of the same size taken {:?}", start.elapsed());

            if log2_floor(poly.size()) % 2 == 0 {
                let log_n = log2_floor(poly.size());
                let omega = poly.omega;
                let mut coeffs = poly.into_coeffs();
                let start = Instant::now();
                crate::plonk::fft::radix_4::best_fft(&mut coeffs, &worker, &omega, log_n as u32);
                println!("Radix-4 FFT of the same size taken {:?}", start.elapsed());
                let to_compare = eval_result.into_coeffs();
                assert!(to_compare == coeffs);
            }


        }
    }
}