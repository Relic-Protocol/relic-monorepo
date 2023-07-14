use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::affine_point_wrapper::aux_data::*;
use franklin_crypto::plonk::circuit::affine_point_wrapper::*;

use franklin_crypto::bellman::SynthesisError;

use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof;
use franklin_crypto::bellman::plonk::better_better_cs::setup::VerificationKey;

use franklin_crypto::plonk::circuit::bigint::RnsParameters;

use franklin_crypto::bellman::pairing::{
    Engine,
    GenericCurveAffine,
};

#[derive(Clone, Debug)]
pub struct ProofGadget<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub num_inputs: usize,
    pub input_values: Vec<AllocatedNum<E>>,
    pub wire_commitments: Vec<WP>,
    pub copy_permutation_grand_product_commitment: WP,
    pub lookup_s_poly_commitment: Option<WP>,
    pub lookup_grand_product_commitment: Option<WP>,
    pub quotient_poly_commitments: Vec<WP>,

    pub wire_values_at_z: Vec<AllocatedNum<E>>,
    pub wire_values_at_z_omega: Vec<AllocatedNum<E>>,
    pub gate_selector_values_at_z: Vec<AllocatedNum<E>>,
    pub copy_grand_product_at_z_omega: AllocatedNum<E>,
    pub lookup_s_poly_opening_at_z_omega: Option<AllocatedNum<E>>,
    pub lookup_grand_product_opening_at_z_omega: Option<AllocatedNum<E>>,
    pub lookup_t_poly_opening_at_z: Option<AllocatedNum<E>>,
    pub lookup_t_poly_opening_at_z_omega: Option<AllocatedNum<E>>,
    pub lookup_selector_poly_opening_at_z: Option<AllocatedNum<E>>,
    pub lookup_table_type_poly_opening_at_z: Option<AllocatedNum<E>>,
    pub quotient_polynomial_at_z: AllocatedNum<E>,
    pub linearization_polynomial_at_z: AllocatedNum<E>,
    pub permutation_polynomials_at_z: Vec<AllocatedNum<E>>,

    pub opening_at_z_proof: WP,
    pub opening_at_z_omega_proof: WP,

    pub has_lookup: bool,

    _m: &'a std::marker::PhantomData<()>,
}


impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> ProofGadget<'a, E, WP> {
    pub fn alloc<CS: ConstraintSystem<E>, C: Circuit<E>, AD: AuxData<E>>(
        cs: &mut CS,
        proof: Proof<E, C>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
        has_lookup: bool,
    ) -> Result<Self, SynthesisError> {
        
        let input_values = proof.inputs.iter().map(|x| {
            AllocatedNum::alloc_input(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_commitments = proof.state_polys_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        assert_eq!(proof.witness_polys_commitments.len(), 0);

        let copy_permutation_grand_product_commitment = WrappedAffinePoint::alloc(cs, Some(proof.copy_permutation_grand_product_commitment), params, aux_data)?;

        let lookup_s_poly_commitment = if has_lookup {
            Some(WrappedAffinePoint::alloc(cs, Some(proof.lookup_s_poly_commitment.expect("missing lookup_s_poly_commitment")), params, aux_data)?)
        } else {
            None
        };
        let lookup_grand_product_commitment = if has_lookup {
            Some(WrappedAffinePoint::alloc(cs, Some(proof.lookup_grand_product_commitment.expect("missing lookup_grand_product_commitment")), params, aux_data)?)
        } else {
            None
        };
        
        let quotient_poly_commitments = proof.quotient_poly_parts_commitments.iter().map(|x| {
            WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data)
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z = proof.state_polys_openings_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let wire_values_at_z_omega = proof.state_polys_openings_at_dilations.iter().map(|(_, _, x)| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        assert_eq!(proof.gate_setup_openings_at_z.len(), 0);

        let gate_selector_values_at_z = proof.gate_selectors_openings_at_z.iter().map(|(_, x)| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let permutation_polynomials_at_z = proof.copy_permutation_polys_openings_at_z.iter().map(|x| {
            AllocatedNum::alloc(cs, || Ok(*x))
        }).collect::<Result<Vec<_>, _>>()?;

        let copy_grand_product_at_z_omega = AllocatedNum::alloc(cs, || Ok(proof.copy_permutation_grand_product_opening_at_z_omega))?;
        let quotient_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.quotient_poly_opening_at_z))?; 
        let linearization_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(proof.linearization_poly_opening_at_z))?;  

        let lookup_s_poly_opening_at_z_omega = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_s_poly_opening_at_z_omega.expect("missing lookup_s_poly_opening_at_z_omega")))?)
        } else {
            None
        };
        let lookup_grand_product_opening_at_z_omega = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_grand_product_opening_at_z_omega.expect("missing lookup_grand_product_opening_at_z_omega")))?)
        } else {
            None
        };
        let lookup_t_poly_opening_at_z = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_t_poly_opening_at_z.expect("missing lookup_t_poly_opening_at_z")))?)
        } else {
            None
        };
        let lookup_t_poly_opening_at_z_omega = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_t_poly_opening_at_z_omega.expect("missing lookup_t_poly_opening_at_z_omega")))?)
        } else {
            None
        };
        let lookup_selector_poly_opening_at_z = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_selector_poly_opening_at_z.expect("missing lookup_selector_poly_opening_at_z")))?)
        } else {
            None
        };
        let lookup_table_type_poly_opening_at_z = if has_lookup {
            Some(AllocatedNum::alloc(cs, || Ok(proof.lookup_table_type_poly_opening_at_z.expect("missing lookup_table_type_poly_opening_at_z")))?)
        } else {
            None
        };

        let opening_at_z_proof = WrappedAffinePoint::alloc(cs, Some(proof.opening_proof_at_z), params, aux_data)?;
        let opening_at_z_omega_proof = WrappedAffinePoint::alloc(cs, Some(proof.opening_proof_at_z_omega), params, aux_data)?;
       
        Ok(ProofGadget {
            num_inputs: proof.n,
            input_values,
            wire_commitments,
            copy_permutation_grand_product_commitment,
            lookup_s_poly_commitment,
            lookup_grand_product_commitment,
            quotient_poly_commitments,

            wire_values_at_z,
            wire_values_at_z_omega,
            gate_selector_values_at_z,
            copy_grand_product_at_z_omega,
            lookup_s_poly_opening_at_z_omega,
            lookup_grand_product_opening_at_z_omega,
            lookup_t_poly_opening_at_z,
            lookup_t_poly_opening_at_z_omega,
            lookup_selector_poly_opening_at_z,
            lookup_table_type_poly_opening_at_z,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,

            opening_at_z_proof,
            opening_at_z_omega_proof,

            has_lookup: has_lookup,
            _m: &std::marker::PhantomData::<()>,
        })
    }

    pub fn alloc_from_witness<CS: ConstraintSystem<E>, C: Circuit<E>, P: PlonkConstraintSystemParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        num_inputs: usize,
        proof: Option<&Proof<E, C>>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        aux_data: &AD,
        has_lookup: bool,
    ) -> Result<Self, SynthesisError> {

        use franklin_crypto::plonk::circuit::Assignment;

        let state_width = P::STATE_WIDTH;
        let num_quotient_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!P::HAS_WITNESS_POLYNOMIALS);

        let mut input_values = vec![];
        for idx in 0..num_inputs {
            let wit = proof.as_ref().and_then(|el| Some(&el.inputs)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            input_values.push(allocated);
        }

        let mut wire_commitments = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.state_polys_commitments)).and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            wire_commitments.push(allocated);
        }

        // TODO: assert_eq!(proof.witness_polys_commitments.len(), 0);
        
        let wit = proof.as_ref().and_then(|el| Some(el.copy_permutation_grand_product_commitment));
        let copy_permutation_grand_product_commitment = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let lookup_s_poly_commitment = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_s_poly_commitment.expect("missing lookup_s_poly_commitment")));
            Some(WrappedAffinePoint::alloc(cs, wit, params, aux_data)?)
        } else {
            None
        };
        let lookup_grand_product_commitment = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_grand_product_commitment.expect("missing lookup_grand_product_commitment")));
            Some(WrappedAffinePoint::alloc(cs, wit, params, aux_data)?)
        } else {
            None
        };

        let mut quotient_poly_commitments = vec![];
        for idx in 0..num_quotient_commitments {
            let wit = proof.as_ref().and_then(|el| Some(&el.quotient_poly_parts_commitments)).and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            quotient_poly_commitments.push(allocated);
        }

        let mut wire_values_at_z = vec![];
        for idx in 0..state_width {
            let wit = proof.as_ref().and_then(|el| Some(&el.state_polys_openings_at_z)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            wire_values_at_z.push(allocated);
        }

        let mut wire_values_at_z_omega = vec![];
        for idx in 0..1 {
            let wit = proof.as_ref().and_then(|el| Some(&el.state_polys_openings_at_dilations)).and_then(|el| Some(el[idx].2));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            wire_values_at_z_omega.push(allocated);
        }

        // TODO: assert_eq!(proof.gate_setup_openings_at_z.len(), 0);

        let mut gate_selector_values_at_z = vec![];
        if P::HAS_CUSTOM_GATES {
            for idx in 0..1 {
                let wit = proof.as_ref().and_then(|el| Some(&el.gate_selectors_openings_at_z)).and_then(|el| Some(el[idx].1));
                let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;
                gate_selector_values_at_z.push(allocated);
            }
        }

        let mut permutation_polynomials_at_z = vec![];
        for idx in 0..(state_width-1) {
            let wit = proof.as_ref().and_then(|el| Some(&el.copy_permutation_polys_openings_at_z)).and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            permutation_polynomials_at_z.push(allocated);
        }

        let wit = proof.as_ref().and_then(|el| Some(el.copy_permutation_grand_product_opening_at_z_omega));
        let copy_grand_product_at_z_omega = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let wit = proof.as_ref().and_then(|el| Some(el.quotient_poly_opening_at_z));
        let quotient_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let wit = proof.as_ref().and_then(|el| Some(el.linearization_poly_opening_at_z));
        let linearization_polynomial_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?; 

        let lookup_s_poly_opening_at_z_omega = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_s_poly_opening_at_z_omega.expect("missing lookup_s_poly_opening_at_z_omega")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };
        let lookup_grand_product_opening_at_z_omega = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_grand_product_opening_at_z_omega.expect("missing lookup_grand_product_opening_at_z_omega")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };
        let lookup_t_poly_opening_at_z = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_t_poly_opening_at_z.expect("missing lookup_t_poly_opening_at_z")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };
        let lookup_t_poly_opening_at_z_omega = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_t_poly_opening_at_z_omega.expect("missing lookup_t_poly_opening_at_z_omega")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };
        let lookup_selector_poly_opening_at_z = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_selector_poly_opening_at_z.expect("missing lookup_selector_poly_opening_at_z")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };
        let lookup_table_type_poly_opening_at_z = if has_lookup {
            let wit = proof.as_ref().and_then(|el| Some(el.lookup_table_type_poly_opening_at_z.expect("missing lookup_table_type_poly_opening_at_z")));
            Some(AllocatedNum::alloc(cs, || Ok(*wit.get()?))?)
        } else {
            None
        };

        let wit = proof.as_ref().and_then(|el| Some(el.opening_proof_at_z));
        let opening_at_z_proof = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let wit = proof.as_ref().and_then(|el| Some(el.opening_proof_at_z_omega));
        let opening_at_z_omega_proof = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        Ok(ProofGadget {
            num_inputs: num_inputs,
            input_values,
            wire_commitments,
            copy_permutation_grand_product_commitment,
            lookup_s_poly_commitment,
            lookup_grand_product_commitment,
            quotient_poly_commitments,

            wire_values_at_z,
            wire_values_at_z_omega,
            gate_selector_values_at_z,
            copy_grand_product_at_z_omega,
            lookup_s_poly_opening_at_z_omega,
            lookup_grand_product_opening_at_z_omega,
            lookup_t_poly_opening_at_z,
            lookup_t_poly_opening_at_z_omega,
            lookup_selector_poly_opening_at_z,
            lookup_table_type_poly_opening_at_z,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,

            opening_at_z_proof,
            opening_at_z_omega_proof,

            has_lookup: has_lookup,
            _m: &std::marker::PhantomData::<()>,
        })
    }
}

#[derive(Clone, Debug)]
pub struct VerificationKeyGadget<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub n: Option<usize>,
    pub domain_size_as_allocated_num: Option<AllocatedNum<E>>,
    pub omega_as_allocated_num: Option<AllocatedNum<E>>,
    pub num_inputs: usize,
    pub gate_setup_commitments: Vec<WP>,
    pub gate_selector_commitments: Vec<WP>,
    pub copy_permutation_commitments: Vec<WP>,
    pub copy_permutation_non_residues: Vec<E::Fr>,
    pub lookup_selector_commitment: Option<WP>,
    pub lookup_tables_commitments: Vec<WP>,
    pub lookup_table_type_commitment: Option<WP>,

    _m: &'a std::marker::PhantomData<()>,
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> VerificationKeyGadget<'a, E, WP> {
    
    pub fn alloc<CS: ConstraintSystem<E>, C: Circuit<E>, AD: AuxData<E>>(
        _cs: &mut CS,
        vk: &VerificationKey<E, C>,
        params: &'a RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>,
        _aux_data: &AD,
    ) -> Result<Self, SynthesisError> {

        let gate_setup_commitments = vk.gate_setup_commitments.iter().map(|x| {
            WrappedAffinePoint::constant(*x, params)
        }).collect::<Vec<_>>();

        let gate_selector_commitments = vk.gate_selectors_commitments.iter().map(|x| {
            WrappedAffinePoint::constant(*x, params)
        }).collect::<Vec<_>>();

        let copy_permutation_commitments = vk.permutation_commitments.iter().map(|x| {
            WrappedAffinePoint::constant(*x, params)
        }).collect::<Vec<_>>();

        let lookup_selector_commitment = if vk.total_lookup_entries_length > 0 {
            Some(WrappedAffinePoint::constant(vk.lookup_selector_commitment.unwrap(), params))
        } else {
            None
        };
        let lookup_tables_commitments = vk.lookup_tables_commitments.iter().map(|x| {
            WrappedAffinePoint::constant(*x, params)
        }).collect::<Vec<_>>();
        let lookup_table_type_commitment = if vk.total_lookup_entries_length > 0 {
            Some(WrappedAffinePoint::constant(vk.lookup_table_type_commitment.unwrap(), params))
        } else {
            None
        };

        Ok(VerificationKeyGadget {
            n : Some(vk.n),
            domain_size_as_allocated_num: None,
            omega_as_allocated_num: None,
            num_inputs : vk.num_inputs,
            gate_setup_commitments,
            gate_selector_commitments,
            copy_permutation_commitments,
            copy_permutation_non_residues: vk.non_residues.clone(),

            lookup_selector_commitment,
            lookup_tables_commitments,
            lookup_table_type_commitment,

            _m: &std::marker::PhantomData::<()>,
        })
    }
}
