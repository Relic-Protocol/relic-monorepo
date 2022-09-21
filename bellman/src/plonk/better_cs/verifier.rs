use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::plonk::domains::*;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::{Proof, VerificationKey};

use crate::source::{DensityTracker, DensityTrackerersChain};

use crate::kate_commitment::*;
use super::utils::*;

use crate::plonk::commitments::transcript::*;

pub fn verify<E: Engine, P: PlonkConstraintSystemParams<E>, T: Transcript<E::Fr>>(
    proof: &Proof<E, P>,
    verification_key: &VerificationKey<E, P>,
    transcript_init_params: Option< <T as Prng<E::Fr> >:: InitializationParameters>,
) -> Result<bool, SynthesisError> {
    let (valid, _) = verify_and_aggregate::<E, P, T>(proof, verification_key, transcript_init_params)?;

    Ok(valid)
}

pub fn verify_and_aggregate<E: Engine, P: PlonkConstraintSystemParams<E>, T: Transcript<E::Fr>>(
    proof: &Proof<E, P>,
    verification_key: &VerificationKey<E, P>,
    transcript_init_params: Option< <T as Prng<E::Fr> >:: InitializationParameters>,
) -> Result<(bool, [E::G1Affine; 2]), SynthesisError> {
    use crate::pairing::CurveAffine;
    use crate::pairing::CurveProjective;

    assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

    let mut transcript = if let Some(p) = transcript_init_params {
        T::new_from_params(p)
    } else {
        T::new()
    };

    if proof.n != verification_key.n {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    if proof.num_inputs != verification_key.num_inputs {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let n = proof.n;
    let required_domain_size = n + 1;
    if required_domain_size.is_power_of_two() == false {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;

    let selector_q_const_index = P::STATE_WIDTH + 1;
    let selector_q_m_index = P::STATE_WIDTH;

    let non_residues = make_non_residues::<E::Fr>(P::STATE_WIDTH - 1);

    // Commit public inputs
    for inp in proof.input_values.iter() {
        transcript.commit_field_element(&inp);
    }

    // Commit wire values
    for w in proof.wire_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &w);
    }

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    // commit grand product
    commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

    let alpha = transcript.get_challenge();

    // Commit parts of the quotient polynomial
    for w in proof.quotient_poly_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &w);
    }

    let z = transcript.get_challenge();
    let mut z_by_omega = z;
    z_by_omega.mul_assign(&domain.generator);

    // commit every claimed value

    for el in proof.wire_values_at_z.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.wire_values_at_z_omega.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.permutation_polynomials_at_z.iter() {
        transcript.commit_field_element(el);
    }

    transcript.commit_field_element(&proof.quotient_polynomial_at_z);

    transcript.commit_field_element(&proof.linearization_polynomial_at_z);

    transcript.commit_field_element(&proof.grand_product_at_z_omega);


    // do the actual check for relationship at z

    {
        let mut lhs = proof.quotient_polynomial_at_z;
        let vanishing_at_z = evaluate_vanishing_for_size(&z, required_domain_size as u64);
        lhs.mul_assign(&vanishing_at_z);

        let mut quotient_linearization_challenge = E::Fr::one();

        let mut rhs = proof.linearization_polynomial_at_z;

        // add public inputs
        {
            for (idx, input) in proof.input_values.iter().enumerate() {
                let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, z)?;
                tmp.mul_assign(&input);

                rhs.add_assign(&tmp);
            }
        }

        quotient_linearization_challenge.mul_assign(&alpha);

        // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

        let mut z_part = proof.grand_product_at_z_omega;

        for (w, p) in proof.wire_values_at_z.iter().zip(proof.permutation_polynomials_at_z.iter()) {
            let mut tmp = *p;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&w);
            
            z_part.mul_assign(&tmp);
        }   

        // last poly value and gamma
        let mut tmp = gamma;
        tmp.add_assign(&proof.wire_values_at_z.iter().rev().next().unwrap());

        z_part.mul_assign(&tmp);
        z_part.mul_assign(&quotient_linearization_challenge);

        rhs.sub_assign(&z_part);

        quotient_linearization_challenge.mul_assign(&alpha);
        
        // - L_0(z) * \alpha^2

        let mut l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;
        l_0_at_z.mul_assign(&quotient_linearization_challenge);

        rhs.sub_assign(&l_0_at_z);

        if lhs != rhs {
            return Ok((false, [E::G1Affine::zero(); 2]));
        }
    }

    let v = transcript.get_challenge();

    commit_point_as_xy::<E, _>(&mut transcript, &proof.opening_at_z_proof);

    commit_point_as_xy::<E, _>(&mut transcript, &proof.opening_at_z_omega_proof);

    let u = transcript.get_challenge();

    let z_in_domain_size = z.pow(&[required_domain_size as u64]);

    // first let's reconstruct the linearization polynomial from
    // honomorphic commitments, and simultaneously add (through the separation scalar "u")
    // part for opening of z(X) at z*omega

    // calculate the power to add z(X) commitment that is opened at x*omega
    // it's r(X) + witness + all permutations + 1
    let v_power_for_standalone_z_x_opening = 1 + 1 + P::STATE_WIDTH + (P::STATE_WIDTH-1);

    let virtual_commitment_for_linearization_poly = {
        let mut r = E::G1::zero();

        // main gate. Does NOT include public inputs
        {
            // Q_const(x)
            r.add_assign_mixed(&verification_key.selector_commitments[selector_q_const_index]);

            for i in 0..P::STATE_WIDTH {
                // Q_k(X) * K(z)
                r.add_assign(&verification_key.selector_commitments[i].mul(proof.wire_values_at_z[i].into_repr()));
            }

            // Q_m(X) * A(z) * B(z)
            let mut scalar = proof.wire_values_at_z[0];
            scalar.mul_assign(&proof.wire_values_at_z[1]);
            r.add_assign(&verification_key.selector_commitments[selector_q_m_index].mul(scalar.into_repr()));

            // Q_d_next(X) * D(z*omega)
            r.add_assign(&verification_key.next_step_selector_commitments[0].mul(proof.wire_values_at_z_omega[0].into_repr()));
        }

        // v * [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() * z(X) -
        // - \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X) +
        // + alpha^2 * L_0(z) * z(X) ] + 
        // + v^{P} * u * z(X)
        // and join alpha^2 * L_0(z) and v^{P} * u into the first term containing z(X)

        // [alpha * (a + beta*z + gamma)(b + beta*k_1*z + gamma)()() + alpha^2 * L_0(z)] * z(X)
        let grand_product_part_at_z = {
            let mut scalar = E::Fr::one();

            // permutation part
            for (wire, non_res) in proof.wire_values_at_z.iter()
                            .zip(Some(E::Fr::one()).iter().chain(&non_residues)) 
            {
                let mut tmp = z;
                tmp.mul_assign(&non_res);
                tmp.mul_assign(&beta);
                tmp.add_assign(&wire);
                tmp.add_assign(&gamma);

                scalar.mul_assign(&tmp);
            }

            scalar.mul_assign(&alpha);

            let l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;

            // + L_0(z) * alpha^2
            let mut tmp = l_0_at_z;
            tmp.mul_assign(&alpha);
            tmp.mul_assign(&alpha);
            scalar.add_assign(&tmp);

            // * v
            // scalar.mul_assign(&v);

            scalar
        };

        // v^{P} * u * z(X)
        let grand_product_part_at_z_omega = {
            // + v^{P} * u
            let mut tmp = v.pow(&[v_power_for_standalone_z_x_opening as u64]);
            tmp.mul_assign(&u);

            tmp
        };

        // \alpha * (a*perm_a(z)*beta + gamma)()()*beta*z(z*omega) * perm_d(X)
        let last_permutation_part_at_z = {
            let mut scalar = E::Fr::one();

            // permutation part
            for (wire, perm_at_z) in proof.wire_values_at_z.iter()
                            .zip(&proof.permutation_polynomials_at_z) 
            {
                let mut tmp = beta;
                tmp.mul_assign(&perm_at_z);
                tmp.add_assign(&wire);
                tmp.add_assign(&gamma);

                scalar.mul_assign(&tmp);
            }

            scalar.mul_assign(&beta);
            scalar.mul_assign(&proof.grand_product_at_z_omega);
            scalar.mul_assign(&alpha);
            // scalar.mul_assign(&v);

            scalar
        };

        {
            let mut tmp = proof.grand_product_commitment.mul(grand_product_part_at_z.into_repr());
            tmp.sub_assign(&verification_key.permutation_commitments.last().unwrap().mul(last_permutation_part_at_z.into_repr()));
            
            r.add_assign(&tmp);
        }

        r.mul_assign(v.into_repr());

        r.add_assign(&proof.grand_product_commitment.mul(grand_product_part_at_z_omega.into_repr()));

        r
    };

    // now check the openings

    let mut multiopening_challenge = E::Fr::one();

    // reassemble a homomorphic commitment

    // aggregate t(X) from parts

    let mut commitments_aggregation = proof.quotient_poly_commitments[0].into_projective();

    let mut current = z_in_domain_size;
    for part in proof.quotient_poly_commitments.iter().skip(1) {
        commitments_aggregation.add_assign(&part.mul(current.into_repr()));
        current.mul_assign(&z_in_domain_size);
    }

    // do the same for linearization
    multiopening_challenge.mul_assign(&v); // to preserve sequence

    commitments_aggregation.add_assign(&virtual_commitment_for_linearization_poly); // v^1 is contained inside

    debug_assert_eq!(multiopening_challenge, v.pow(&[1 as u64]));

    // do the same for wires
    for com in proof.wire_commitments.iter() {
        multiopening_challenge.mul_assign(&v); // v^{1+STATE_WIDTH}
        let tmp = com.mul(multiopening_challenge.into_repr());
        commitments_aggregation.add_assign(&tmp);
    }

    debug_assert_eq!(multiopening_challenge, v.pow(&[1 + 4 as u64]));

    // and for all permutation polynomials except the last one
    assert_eq!(verification_key.permutation_commitments.len(), proof.permutation_polynomials_at_z.len() + 1);

    for com in verification_key.permutation_commitments[0..(verification_key.permutation_commitments.len() - 1)].iter() {
        multiopening_challenge.mul_assign(&v); // v^{1+STATE_WIDTH + STATE_WIDTH - 1}
        let tmp = com.mul(multiopening_challenge.into_repr());
        commitments_aggregation.add_assign(&tmp);
    }

    multiopening_challenge.mul_assign(&v); // we skip z(X) at z

    // aggregate last wire commitment (that is opened at z*omega)
    // using multiopening challenge and u
    multiopening_challenge.mul_assign(&v);
    let mut scalar = multiopening_challenge;
    scalar.mul_assign(&u);
    commitments_aggregation.add_assign(&proof.wire_commitments.last().unwrap().mul(scalar.into_repr()));

    // subtract the opening value using one multiplication

    let mut multiopening_challenge_for_values = E::Fr::one();
    let mut aggregated_value = proof.quotient_polynomial_at_z;
    for value_at_z in Some(proof.linearization_polynomial_at_z).iter()
            .chain(&proof.wire_values_at_z)
            .chain(&proof.permutation_polynomials_at_z) 
        {
            multiopening_challenge_for_values.mul_assign(&v);   
            let mut tmp = *value_at_z;
            tmp.mul_assign(&multiopening_challenge_for_values);
            aggregated_value.add_assign(&tmp);
        }

    // add parts that are opened at z*omega using `u`
    {
        multiopening_challenge_for_values.mul_assign(&v);  
        let mut scalar = multiopening_challenge_for_values;
        scalar.mul_assign(&u);
        let mut tmp = proof.grand_product_at_z_omega;
        tmp.mul_assign(&scalar);

        aggregated_value.add_assign(&tmp);
    }
    {
        multiopening_challenge_for_values.mul_assign(&v);  
        let mut scalar = multiopening_challenge_for_values;
        scalar.mul_assign(&u);
        let mut tmp = proof.wire_values_at_z_omega[0];
        tmp.mul_assign(&scalar);

        aggregated_value.add_assign(&tmp);
    }

    assert_eq!(multiopening_challenge, multiopening_challenge_for_values);

    // make equivalent of (f(x) - f(z))
    commitments_aggregation.sub_assign(&E::G1Affine::one().mul(aggregated_value.into_repr()));

    // now check that
    // e(proof_for_z + u*proof_for_z_omega, g2^x) = e(z*proof_for_z + z*omega*u*proof_for_z_omega + (aggregated_commitment - aggregated_opening), g2^1) 
    // with a corresponding change of sign

    let mut pair_with_generator = commitments_aggregation;

    pair_with_generator.add_assign(&proof.opening_at_z_proof.mul(z.into_repr()));
    let mut scalar = z_by_omega;
    scalar.mul_assign(&u);
    pair_with_generator.add_assign(&proof.opening_at_z_omega_proof.mul(scalar.into_repr()));

    let mut pair_with_x = proof.opening_at_z_omega_proof.mul(u.into_repr());
    pair_with_x.add_assign_mixed(&proof.opening_at_z_proof);
    pair_with_x.negate();

    let pair_with_generator = pair_with_generator.into_affine();
    let pair_with_x = pair_with_x.into_affine();

    let valid = E::final_exponentiation(
        &E::miller_loop(&[
            (&pair_with_generator.prepare(), &verification_key.g2_elements[0].prepare()),
            (&pair_with_x.prepare(), &verification_key.g2_elements[1].prepare())
        ])
    ).unwrap() == E::Fqk::one();

    Ok((valid, [pair_with_generator, pair_with_x]))
}