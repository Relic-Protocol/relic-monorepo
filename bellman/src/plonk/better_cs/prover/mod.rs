use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::plonk::domains::*;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::{SetupPolynomials, Proof, SetupPolynomialsPrecomputations};

use crate::source::{DensityTracker, DensityTrackerersChain};

use crate::kate_commitment::*;
use super::utils::*;

use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

use super::LDE_FACTOR;

pub(crate) mod prove_steps;

// #[derive(Debug, Clone)]
pub struct ProverAssembly<E: Engine, P: PlonkConstraintSystemParams<E>> {
    m: usize,
    n: usize,
    // input_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,
    // aux_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    wire_assignments: Vec<Vec<E::Fr>>,

    // aux_densities: Vec<DensityTracker>,

    inputs_map: Vec<usize>,
    dummy_var: Variable,

    is_finalized: bool,

    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ConstraintSystem<E, P> for ProverAssembly<E, P> {
    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_inputs += 1;
        let index = self.num_inputs;
        self.input_assingments.push(value);

        let input_var = Variable(Index::Input(index));

        // there is an implicit gate to constraint the input
        // and it's handled during the proving 
        self.n += 1; 

        Ok(input_var)

    }

    // allocate an abstract gate
    fn new_gate(&mut self, 
        variables: P::StateVariables, 
        _this_step_coeffs: P::ThisTraceStepCoefficients,
        _next_step_coeffs: P::NextTraceStepCoefficients
    ) -> Result<(), SynthesisError>
    {
        for (idx, &v) in variables.as_ref().iter().enumerate() {
            let val = self.get_value(v)?;
            self.wire_assignments[idx].push(val);
        }
        self.n += 1;

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                unreachable!();
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(input)) => {
                self.input_assingments[input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[aux - 1]
            }
        };

        Ok(value)
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ProverAssembly<E, P> {
    pub fn new() -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            wire_assignments: vec![vec![]; P::STATE_WIDTH],
        
            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }

    pub fn new_with_size_hints(num_inputs: usize, num_aux: usize) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: Vec::with_capacity(num_inputs),
            aux_assingments: Vec::with_capacity(num_aux),

            wire_assignments: vec![Vec::with_capacity(num_inputs + num_aux); P::STATE_WIDTH],
        
            // aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: Vec::with_capacity(num_inputs),
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn num_gates(&self) -> usize {
        self.n
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let n = self.n;
        if (n+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        self.n = (n+1).next_power_of_two() - 1;

        self.is_finalized = true;
    }

    // pub fn make_witness_polynomials(
    //     self
    // ) -> Result<(Vec<Vec<E::Fr>>, Vec<DensityTracker>), SynthesisError>
    // {
    //     assert!(self.is_finalized);

    //     let mut full_assignments = vec![Vec::with_capacity((self.n+1).next_power_of_two()); self.wire_assignments.len()];

    //     for inp in self.input_assingments.into_iter() {
    //         // inputs will always go into A wire
    //         full_assignments[0].push(inp);
    //         for i in 1..full_assignments.len() {
    //             full_assignments[i].push(E::Fr::zero());
    //         }
    //     }

    //     for (idx, aux) in self.wire_assignments.into_iter().enumerate() {
    //         full_assignments[idx].extend(aux);
    //         full_assignments[idx].resize((self.n+1).next_power_of_two() - 1, E::Fr::zero());
    //     }

    //     let mut aux_densities = self.aux_densities;

    //     for d in aux_densities.iter_mut() {
    //         d.pad((self.n+1).next_power_of_two() - 1);
    //     }

    //     for a in full_assignments.iter() {
    //         assert_eq!(a.len(), (self.n+1).next_power_of_two() - 1);
    //     }

    //     Ok((full_assignments, aux_densities))
    // }

    pub fn make_witness_polynomials(
        self
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);

        let mut full_assignments = vec![Vec::with_capacity((self.n+1).next_power_of_two()); self.wire_assignments.len()];

        for inp in self.input_assingments.into_iter() {
            // inputs will always go into A wire
            full_assignments[0].push(inp);
            for i in 1..full_assignments.len() {
                full_assignments[i].push(E::Fr::zero());
            }
        }

        for (idx, aux) in self.wire_assignments.into_iter().enumerate() {
            full_assignments[idx].extend(aux);
            full_assignments[idx].resize((self.n+1).next_power_of_two() - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), (self.n+1).next_power_of_two() - 1);
        }

        Ok(full_assignments)
    }
}

// later we can alias traits
// pub trait PlonkCsWidth3WithNextStep<E: Engine> = ConstraintSystem<E, PlonkCsWidth3WithNextStepParams>;

pub type ProverAssembly3WithNextStep<E> = ProverAssembly<E, PlonkCsWidth3WithNextStepParams>;
pub type ProverAssembly4WithNextStep<E> = ProverAssembly<E, PlonkCsWidth4WithNextStepParams>;

impl<E: Engine> ProverAssembly4WithNextStep<E> {
    pub fn prove<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>, CPI: CTPrecomputations<E::Fr>>(
        self, 
        worker: &Worker, 
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
        crs_vals: &Crs<E, CrsForLagrangeForm>, 
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        omegas_inv_bitreversed: &CPI,
        transcript_init_params: Option< <T as Prng<E::Fr> >:: InitializationParameters>,
    ) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
        use crate::pairing::CurveAffine;
        use std::sync::Arc;

        let mut transcript = if let Some(p) = transcript_init_params {
            T::new_from_params(p)
        } else {
            T::new()
        };
            
        assert!(self.is_finalized);

        let input_values = self.input_assingments.clone();

        for inp in input_values.iter() {
            transcript.commit_field_element(inp);
        }

        let n = self.n;
        let num_inputs = self.num_inputs;

        let required_domain_size = n + 1;
        assert!(required_domain_size.is_power_of_two());

        let full_assignments = self.make_witness_polynomials()?;

        let mut proof = Proof::<E, PlonkCsWidth4WithNextStepParams>::empty();
        proof.n = n;
        proof.num_inputs = num_inputs;
        proof.input_values = input_values.clone();

        let coset_factor = E::Fr::multiplicative_generator();

        // let coset_factor = E::Fr::one();

        // Commit wire polynomials 

        for wire_poly in full_assignments.iter() {
            let commitment = commit_using_raw_values(
                &wire_poly, 
                &crs_vals, 
                &worker
            )?;

            commit_point_as_xy::<E, _>(&mut transcript, &commitment);

            proof.wire_commitments.push(commitment);
        }

        // now transform assignments in the polynomials

        let mut assignment_polynomials = vec![];
        for p in full_assignments.into_iter() {
            let p = Polynomial::from_values_unpadded(p)?;
            assignment_polynomials.push(p);
        }

        // make grand product polynomials

        // draw challenges for grand products

        let beta = transcript.get_challenge();
        let gamma = transcript.get_challenge();

        let mut grand_products_protos_with_gamma = assignment_polynomials.clone();

        // add gamma here to save computations later
        for p in grand_products_protos_with_gamma.iter_mut() {
            p.add_constant(&worker, &gamma);
        }

        let domain = Domain::new_for_size(required_domain_size as u64)?;

        let mut domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, 
            &worker
        );

        domain_elements.pop().expect("must pop last element for omega^i");

        let mut domain_elements_poly_by_beta = Polynomial::from_values_unpadded(domain_elements)?;
        domain_elements_poly_by_beta.scale(&worker, beta);

        let non_residues = make_non_residues::<E::Fr>(
            <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH - 1
        );

        // we take A, B, C, ... values and form (A + beta * X * non_residue + gamma), etc and calculate their grand product

        let mut z_num = {
            let mut grand_products_proto_it = grand_products_protos_with_gamma.iter().cloned();

            let mut z_1 = grand_products_proto_it.next().unwrap();
            z_1.add_assign(&worker, &domain_elements_poly_by_beta);

            for (mut p, non_res) in grand_products_proto_it.zip(non_residues.iter()) {
                p.add_assign_scaled(&worker, &domain_elements_poly_by_beta, non_res);
                z_1.mul_assign(&worker, &p);
            }

            z_1
        };

        // we take A, B, C, ... values and form (A + beta * perm_a + gamma), etc and calculate their grand product

        let z_den = {
            assert_eq!(
                setup_precomputations.permutation_polynomials_values_of_size_n_minus_one.len(), 
                grand_products_protos_with_gamma.len()
            );
            let mut grand_products_proto_it = grand_products_protos_with_gamma.into_iter();
            let mut permutation_polys_it = setup_precomputations.permutation_polynomials_values_of_size_n_minus_one.iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(&worker, &permutation_polys_it.next().unwrap(), &beta);

            for (mut p, perm) in grand_products_proto_it
                                            .zip(permutation_polys_it) {
                // permutation polynomials 
                p.add_assign_scaled(&worker, &perm, &beta);
                z_2.mul_assign(&worker, &p);
            }

            z_2.batch_inversion(&worker)?;

            z_2
        };

        z_num.mul_assign(&worker, &z_den);
        drop(z_den);

        let z = z_num.calculate_shifted_grand_product(&worker)?;

        assert!(z.size().is_power_of_two());

        assert!(z.as_ref()[0] == E::Fr::one());
        // println!("Z last = {}", z.as_ref().last().unwrap());
        // assert!(z.as_ref().last().expect("must exist") == &E::Fr::one());

        let z_commitment = commit_using_values(
            &z, 
            &crs_vals, 
            &worker
        )?;
        proof.grand_product_commitment = z_commitment;

        commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

        // interpolate on the main domain
        let z_in_monomial_form = z.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // those are z(x*Omega) formally
        let mut z_shifted_in_monomial_form = z_in_monomial_form.clone();
        z_shifted_in_monomial_form.distribute_powers(&worker, z_in_monomial_form.omega);
        
        // now we have to LDE everything and compute quotient polynomial
        // also to save on openings that we will have to do from the monomial form anyway

        let mut witness_polys_in_monomial_form = vec![];

        let mut witness_ldes_on_coset = vec![];
        let mut witness_next_ldes_on_coset = vec![];

        for (idx, w) in assignment_polynomials.into_iter().enumerate() {
            let monomial = w.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
            witness_polys_in_monomial_form.push(monomial.clone());

            // this is D polynomial and we need to make next
            if idx == <PlonkCsWidth4WithNextStepParams as PlonkConstraintSystemParams<E>>::STATE_WIDTH - 1 {
                let mut d_next = monomial.clone();
                d_next.distribute_powers(&worker, d_next.omega);

                let lde = d_next.bitreversed_lde_using_bitreversed_ntt(
                    &worker, 
                    LDE_FACTOR, 
                    omegas_bitreversed, 
                    &coset_factor
                )?;

                witness_next_ldes_on_coset.push(lde);
            }

            let lde = monomial.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;
            witness_ldes_on_coset.push(lde);
        }

        let alpha = transcript.get_challenge();

        // calculate first part of the quotient polynomial - the gate itself
        // A + B + C + D + AB + CONST + D_NEXT == 0 everywhere but on the last point of the domain

        let mut quotient_linearization_challenge = E::Fr::one();

        let (mut t_1, mut tmp) = {
            // Include the public inputs
            let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(required_domain_size)?;
            for (idx, &input) in input_values.iter().enumerate() {
                inputs_poly.as_mut()[idx] = input;
            }
            // go into monomial form

            let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

            // add constants selectors vector
            inputs_poly.add_assign(&worker, setup.selector_polynomials.last().unwrap());

            // LDE
            let mut t_1 = inputs_poly.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;

            // Q_A * A
            let mut tmp = setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[0].clone();
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            // Q_B * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[1]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            // Q_C * C
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[2]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[2]);
            t_1.add_assign(&worker, &tmp);

            // Q_D * D
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[3]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[3]);
            t_1.add_assign(&worker, &tmp);

            // Q_M * A * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[4]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            tmp.reuse_allocation(&setup_precomputations.next_step_selector_polynomials_on_coset_of_size_4n_bitreversed[0]);
            tmp.mul_assign(&worker, &witness_next_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            (t_1, tmp)
        };

        // drop(witness_ldes_on_coset);
        drop(witness_next_ldes_on_coset);

        // now compute the permutation argument

        let z_coset_lde_bitreversed = z_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            LDE_FACTOR, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        assert!(z_coset_lde_bitreversed.size() == required_domain_size*LDE_FACTOR);

        let z_shifted_coset_lde_bitreversed = z_shifted_in_monomial_form.bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            LDE_FACTOR, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size*LDE_FACTOR);

        // For both Z_1 and Z_2 we first check for grand products
        // z*(X)(A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma) - 
        // - (A + beta*perm_a(X) + gamma)(B + beta*perm_b(X) + gamma)(C + beta*perm_c(X) + gamma)*Z(X*Omega)== 0

        // we use evaluations of the polynomial X and K_i * X on a large domain's coset

        quotient_linearization_challenge.mul_assign(&alpha);

        {
            let mut contrib_z = z_coset_lde_bitreversed.clone();

            // A + beta*X + gamma

            tmp.reuse_allocation(&witness_ldes_on_coset[0]);
            tmp.add_constant(&worker, &gamma);
            tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &beta);
            contrib_z.mul_assign(&worker, &tmp);

            assert_eq!(non_residues.len() + 1, witness_ldes_on_coset.len());

            for (w, non_res) in witness_ldes_on_coset[1..].iter().zip(non_residues.iter()) {
                let mut factor = beta;
                factor.mul_assign(&non_res);

                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &factor);
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_1.add_assign_scaled(&worker, &contrib_z, &quotient_linearization_challenge);

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            assert_eq!(
                setup_precomputations.permutation_polynomials_on_coset_of_size_4n_bitreversed.len(), witness_ldes_on_coset.len()
            );

            for (w, perm) in witness_ldes_on_coset.iter()
            .zip(setup_precomputations.permutation_polynomials_on_coset_of_size_4n_bitreversed.iter()) {
                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &perm, &beta);
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_1.sub_assign_scaled(&worker, &contrib_z, &quotient_linearization_challenge);

            drop(contrib_z);
        }

        quotient_linearization_challenge.mul_assign(&alpha);

        // z(omega^0) - 1 == 0

        let l_0 = calculate_lagrange_poly::<E::Fr>(&worker, required_domain_size.next_power_of_two(), 0)?;

        {
            let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
            z_minus_one_by_l_0.sub_constant(&worker, &E::Fr::one());

            let l_coset_lde_bitreversed = l_0.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                LDE_FACTOR, 
                omegas_bitreversed, 
                &coset_factor
            )?;

            z_minus_one_by_l_0.mul_assign(&worker, &l_coset_lde_bitreversed);

            t_1.add_assign_scaled(&worker, &z_minus_one_by_l_0, &quotient_linearization_challenge);

            drop(z_minus_one_by_l_0);
        }

        drop(tmp);

        t_1.mul_assign(&worker, &setup_precomputations.inverse_divisor_on_coset_of_size_4n_bitreversed);

        t_1.bitreverse_enumeration(&worker);

        let t_poly_in_monomial_form = t_1.icoset_fft_for_generator(&worker, &E::Fr::multiplicative_generator());

        let mut t_poly_parts = t_poly_in_monomial_form.break_into_multiples(required_domain_size)?;

        for t_part in t_poly_parts.iter() {
            let t_part_commitment = commit_using_monomials(
                &t_part, 
                &crs_mon, 
                &worker
            )?;

            commit_point_as_xy::<E, _>(&mut transcript, &t_part_commitment);

            proof.quotient_poly_commitments.push(t_part_commitment);
        }

        // draw random point

        let z = transcript.get_challenge();
        let mut z_by_omega = z;
        z_by_omega.mul_assign(&domain.generator);

        for (idx, p) in witness_polys_in_monomial_form.iter().enumerate() {
            let value_at_z = p.evaluate_at(&worker, z);
            proof.wire_values_at_z.push(value_at_z);
            if idx == 3 {
                let value_at_z_omega = p.evaluate_at(&worker, z_by_omega);
                proof.wire_values_at_z_omega.push(value_at_z_omega);
            }
        }

        for p in setup.permutation_polynomials[..(setup.permutation_polynomials.len() - 1)].iter() {
            let value_at_z = p.evaluate_at(&worker, z);
            proof.permutation_polynomials_at_z.push(value_at_z);
        }

        let z_at_z_omega = z_in_monomial_form.evaluate_at(&worker, z_by_omega);
        proof.grand_product_at_z_omega = z_at_z_omega;

        let t_at_z = {
            let mut result = E::Fr::zero();
            let mut current = E::Fr::one();
            let z_in_domain_size = z.pow(&[required_domain_size as u64]);
            for p in t_poly_parts.iter() {
                let mut subvalue_at_z = p.evaluate_at(&worker, z);
                subvalue_at_z.mul_assign(&current);
                result.add_assign(&subvalue_at_z);
                current.mul_assign(&z_in_domain_size);
            }

            result
        };

        proof.quotient_polynomial_at_z = t_at_z;

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

        // now compute linearization_polynomial in a monomial form

        let mut quotient_linearization_challenge = E::Fr::one();

        let r = {
            // Q_const
            let mut r = setup.selector_polynomials[5].clone();

            // Q_A * A(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[0], &proof.wire_values_at_z[0]);

            // Q_B * B(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[1], &proof.wire_values_at_z[1]);

            // Q_C * C(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[2], &proof.wire_values_at_z[2]);

            // Q_D * D(z)
            r.add_assign_scaled(&worker, &setup.selector_polynomials[3], &proof.wire_values_at_z[3]);

            // Q_M * A(z) * B(z)
            let mut scaling_factor = proof.wire_values_at_z[0];
            scaling_factor.mul_assign(&proof.wire_values_at_z[1]);
            r.add_assign_scaled(&worker, &setup.selector_polynomials[4], &scaling_factor);

            // Q_D_Next * D(z*omega)

            r.add_assign_scaled(&worker, &setup.next_step_selector_polynomials[0], &proof.wire_values_at_z_omega[0]);

            quotient_linearization_challenge.mul_assign(&alpha);

            // + (a(z) + beta*z + gamma)*()*()*()*Z(x)

            let mut factor = quotient_linearization_challenge;
            for (wire_at_z, non_residue) in proof.wire_values_at_z.iter()
                            .zip(Some(E::Fr::one()).iter().chain(&non_residues)) 
            {
                let mut t = z;
                t.mul_assign(&non_residue);
                t.mul_assign(&beta);
                t.add_assign(&wire_at_z);
                t.add_assign(&gamma);

                factor.mul_assign(&t);
            }

            r.add_assign_scaled(&worker, &z_in_monomial_form, &factor);

            // - (a(z) + beta*perm_a + gamma)*()*()*z(z*omega) * beta * perm_d(X)

            let mut factor = quotient_linearization_challenge;
            factor.mul_assign(&beta);
            factor.mul_assign(&z_at_z_omega);

            for (wire_at_z, perm_at_z) in proof.wire_values_at_z.iter()
                            .zip(proof.permutation_polynomials_at_z.iter())
            {
                let mut t = *perm_at_z;
                t.mul_assign(&beta);
                t.add_assign(&wire_at_z);
                t.add_assign(&gamma);

                factor.mul_assign(&t);
            }

            r.sub_assign_scaled(&worker, &setup.permutation_polynomials.last().expect("last permutation poly"), &factor);

            // + L_0(z) * Z(x)

            quotient_linearization_challenge.mul_assign(&alpha);

            let mut factor = evaluate_l0_at_point(required_domain_size as u64, z)?;
            factor.mul_assign(&quotient_linearization_challenge);

            r.add_assign_scaled(&worker, &z_in_monomial_form, &factor);

            r
        };

        // commit the linearization polynomial

        let r_at_z = r.evaluate_at(&worker, z);
        proof.linearization_polynomial_at_z = r_at_z;

        transcript.commit_field_element(&proof.linearization_polynomial_at_z);

        transcript.commit_field_element(&proof.grand_product_at_z_omega);

        // sanity check - verification
        {
            let mut lhs = t_at_z;
            let vanishing_at_z = evaluate_vanishing_for_size(&z ,required_domain_size as u64);
            lhs.mul_assign(&vanishing_at_z);

            let mut quotient_linearization_challenge = E::Fr::one();

            let mut rhs = r_at_z;

            // add public inputs
            {
                for (idx, input) in input_values.iter().enumerate() {
                    let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, z)?;
                    tmp.mul_assign(&input);

                    rhs.add_assign(&tmp);
                }
            }

            quotient_linearization_challenge.mul_assign(&alpha);

            // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

            let mut z_part = z_at_z_omega;

            assert_eq!(proof.permutation_polynomials_at_z.len() + 1, proof.wire_values_at_z.len());

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
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        // get multiopening challenge

        let v = transcript.get_challenge();

        // open at z:
        // t_i(x) * z^{domain_size*i}
        // r(x)
        // witnesses
        // permutations except of the last one

        // open at z*omega:
        // z(x)
        // next step witnesses (if any)

        let mut multiopening_challenge = E::Fr::one();

        let mut poly_to_divide_at_z = t_poly_parts.drain(0..1).collect::<Vec<_>>().pop().unwrap();
        let z_in_domain_size = z.pow(&[required_domain_size as u64]);
        let mut power_of_z = z_in_domain_size;
        for t_part in t_poly_parts.into_iter() {
            poly_to_divide_at_z.add_assign_scaled(&worker, &t_part, &power_of_z);
            power_of_z.mul_assign(&z_in_domain_size);
        }

        // linearization polynomial
        multiopening_challenge.mul_assign(&v);
        poly_to_divide_at_z.add_assign_scaled(&worker, &r, &multiopening_challenge);

        debug_assert_eq!(multiopening_challenge, v.pow(&[1 as u64]));

        // all witness polys
        for w in witness_polys_in_monomial_form.iter() {
            multiopening_challenge.mul_assign(&v);
            poly_to_divide_at_z.add_assign_scaled(&worker, &w, &multiopening_challenge);
        }

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4) as u64]));

        // all except of the last permutation polys
        for p in setup.permutation_polynomials[..(setup.permutation_polynomials.len() - 1)].iter() {
            multiopening_challenge.mul_assign(&v);
            poly_to_divide_at_z.add_assign_scaled(&worker, &p, &multiopening_challenge);
        }

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4 + 3) as u64]));

        multiopening_challenge.mul_assign(&v);

        let mut poly_to_divide_at_z_omega = z_in_monomial_form;
        poly_to_divide_at_z_omega.scale(&worker, multiopening_challenge);

        multiopening_challenge.mul_assign(&v);

        // d should be opened at z*omega due to d_next
        poly_to_divide_at_z_omega.add_assign_scaled(&worker, &witness_polys_in_monomial_form[3], &multiopening_challenge);
        drop(witness_polys_in_monomial_form);

        debug_assert_eq!(multiopening_challenge, v.pow(&[(1 + 4 + 3 + 1 + 1) as u64]));

        // division in monomial form is sequential, so we parallelize the divisions

        let mut polys = vec![(poly_to_divide_at_z, z), (poly_to_divide_at_z_omega, z_by_omega)];

        worker.scope(polys.len(), |scope, chunk| {
            for p in polys.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    let (poly, at) = &p[0];
                    let at = *at;
                    let result = divide_single::<E>(poly.as_ref(), at);
                    p[0] = (Polynomial::from_coeffs(result).unwrap(), at);
                });
            }
        });

        let open_at_z_omega = polys.pop().unwrap().0;
        let open_at_z = polys.pop().unwrap().0;

        let opening_at_z = commit_using_monomials(
            &open_at_z, 
            &crs_mon,
            &worker
        )?;

        let opening_at_z_omega = commit_using_monomials(
            &open_at_z_omega, 
            &crs_mon,
            &worker
        )?;

        proof.opening_at_z_proof = opening_at_z;
        proof.opening_at_z_omega_proof = opening_at_z_omega;
        
        Ok(proof)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::verifier::verify;

    use crate::pairing::Engine;

    #[derive(Clone)]
    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams> >(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc_input(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc_input(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let zero = E::Fr::zero();

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            let dummy = cs.get_dummy_variable();

            // 2a - b == 0
            cs.new_gate(
                [a, b, dummy, dummy], 
                [two, negative_one, zero, zero, zero, zero],
                [zero]
            )?;

            // try various combinations
            cs.new_gate(
                [dummy, b, dummy, a], 
                [zero, negative_one, zero, two, zero, zero],
                [zero]
            )?;

            cs.new_gate(
                [dummy, b, a, dummy], 
                [zero, negative_one, two, zero, zero, zero],
                [zero]
            )?;

            // 10b - c = 0
            let ten = E::Fr::from_str("10").unwrap();

            cs.new_gate(
                [b, c, dummy, dummy], 
                [ten, negative_one, zero, zero, zero, zero],
                [zero]
            )?;

            // same, try various combinations

            cs.new_gate(
                [dummy, c, dummy, b], 
                [zero, negative_one, zero, ten, zero, zero],
                [zero]
            )?;

            cs.new_gate(
                [dummy, c, b, dummy], 
                [zero, negative_one, ten, zero, zero, zero],
                [zero]
            )?;

            // c - a*b == 0 

            cs.new_gate(
                [a, b, dummy, c], 
                [zero, zero, zero, negative_one, one, zero],
                [zero]
            )?;

            cs.new_gate(
                [a, b, c, dummy], 
                [zero, zero, negative_one, zero, one, zero],
                [zero]
            )?;

            // 10a + 10b - c - d == 0

            cs.new_gate(
                [a, b, c, d], 
                [ten, ten, negative_one, negative_one, zero, zero],
                [zero]
            )?;

            cs.new_gate(
                [a, d, b, c], 
                [ten, negative_one, ten, negative_one, zero, zero],
                [zero]
            )?;

            // 2d - c == 0

            cs.new_gate(
                [d, c, dummy, dummy], 
                [two, negative_one, zero, zero, zero, zero],
                [zero]
            )?;

            cs.new_gate(
                [d, c, dummy, d], 
                [one, negative_one, zero, one, zero, zero],
                [zero]
            )?;

            // make a gate that affects next step

            // 10a + 10b - c - (something in d on next step) == 0, then
            // d + 0 + 0 - d = 0

            cs.new_gate(
                [a, b, c, dummy], 
                [ten, ten, negative_one, zero, zero, zero],
                [negative_one]
            )?;

            cs.new_gate(
                [d, dummy, dummy, d], 
                [one, zero, zero, negative_one, zero, zero],
                [zero]
            )?;

            // check internal constant

            cs.new_gate(
                [d, dummy, dummy, dummy], 
                [negative_one, zero, zero, zero, zero, E::Fr::from_str("100").unwrap()],
                [zero]
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_prove_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;
        use crate::plonk::better_cs::generator::*;
        use crate::plonk::better_cs::keys::*;

        let mut assembly = GeneratorAssembly4WithNextStep::<Bn256>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.clone().synthesize(&mut assembly).expect("must work");

        // println!("{:?}", assembly);

        assembly.finalize();

        let worker = Worker::new();

        let setup = assembly.setup(&worker).unwrap();

        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<Bn256, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key = VerificationKey::from_setup(
            &setup, 
            &worker, 
            &crs_mons
        ).unwrap();

        // println!("Verification key = {:?}", verification_key);

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).unwrap();

        let mut assembly = ProverAssembly4WithNextStep::<Bn256>::new();

        circuit.clone().synthesize(&mut assembly).expect("must work");

        assembly.finalize();

        let size = setup.permutation_polynomials[0].size();

        type Transcr = Blake2sTranscript<Fr>;

        let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());

        let proof = assembly.prove::<Transcr, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
            None,
        ).unwrap();

        let is_valid = verify::<Bn256, PlonkCsWidth4WithNextStepParams, Transcr>(&proof, &verification_key, None).unwrap();

        assert!(is_valid);

    }
}