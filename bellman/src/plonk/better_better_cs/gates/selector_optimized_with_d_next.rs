use super::*;

#[derive(Clone, Debug, Hash, Default)]
pub struct SelectorOptimizedWidth4MainGateWithDNext;

impl SelectorOptimizedWidth4MainGateWithDNext {
    pub const AB_MULTIPLICATION_TERM_COEFF_INDEX: usize = 4;
    pub const AC_MULTIPLICATION_TERM_COEFF_INDEX: usize = 5;
    pub const CONSTANT_TERM_COEFF_INDEX: usize = 6;
    pub const D_NEXT_TERM_COEFF_INDEX: usize = 7;
}

impl<E: Engine> GateInternal<E> for SelectorOptimizedWidth4MainGateWithDNext {
    fn name(&self) -> &'static str {
        "main gate of width 4 with D_next and selector optimization"
    }

    fn degree(&self) -> usize {
        3
    }

    fn can_include_public_inputs(&self) -> bool {
        true
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 2)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 3)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 4)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 5)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 6)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 7)),

            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),

            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolyIdentifier::GateSetupPolynomial(name, 0),
            PolyIdentifier::GateSetupPolynomial(name, 1),
            PolyIdentifier::GateSetupPolynomial(name, 2),
            PolyIdentifier::GateSetupPolynomial(name, 3),
            PolyIdentifier::GateSetupPolynomial(name, 4),
            PolyIdentifier::GateSetupPolynomial(name, 5),
            PolyIdentifier::GateSetupPolynomial(name, 6),
            PolyIdentifier::GateSetupPolynomial(name, 7),
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
            PolyIdentifier::VariablesPolynomial(3),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        true
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 2)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 3)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 4)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 5)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 6)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 7)),
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),

            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        1
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        let name = <Self as GateInternal<E>>::name(&self);

        let q_a = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 0), row);
        let q_b = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 1), row);
        let q_c = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 2), row);
        let q_d = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 3), row);
        let q_m_ab = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, Self::AB_MULTIPLICATION_TERM_COEFF_INDEX), row);
        let q_m_ac = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, Self::AC_MULTIPLICATION_TERM_COEFF_INDEX), row);
        let q_const = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, Self::CONSTANT_TERM_COEFF_INDEX), row);
        let q_d_next = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 7), row);

        // println!("{}*A + {}*B + {}*C + {}*D + {} + {}*A*B + {}*A*C {}*D_next", q_a, q_b, q_c, q_d, q_const, q_m_ab, q_m_ac, q_d_next);
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = if last_row == false {
            Some(poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1))
        } else {
            None
        }; 

        // println!("A = {}, B = {}, C = {}, D = {}, D_Next = {:?}", a_value, b_value, c_value, d_value, d_next_value);

        let mut total = E::Fr::zero();

        for (q, v) in [a_value, b_value, c_value, d_value].iter()
                    .zip([q_a, q_b, q_c, q_d].iter())
        {
            let mut tmp = *q;
            tmp.mul_assign(v);
            total.add_assign(&tmp);
        }

        total.add_assign(&q_const);

        let mut tmp = q_m_ab;
        tmp.mul_assign(&a_value);
        tmp.mul_assign(&b_value);
        total.add_assign(&tmp);

        let mut tmp = q_m_ac;
        tmp.mul_assign(&a_value);
        tmp.mul_assign(&c_value);
        total.add_assign(&tmp);

        if last_row == false {
            let mut tmp = d_next_value.expect("must be able to get d_next");
            tmp.mul_assign(&q_d_next);

            total.add_assign(&tmp);
        } else {
            assert!(q_d_next.is_zero());
        }

        if !total.is_zero() {
            println!("{}*A + {}*B + {}*C + {}*D + {} + {}*A*B + {}*A*C + {}*D_next", q_a, q_b, q_c, q_d, q_const, q_m_ab, q_m_ac, q_d_next);
            println!("A = {}, B = {}, C = {}, D = {}, D_Next = {:?}", a_value, b_value, c_value, d_value, d_next_value);
        }

        total
    }

    fn contribute_into_quotient(
        &self, 
        _domain_size: usize,
        _poly_storage: &mut AssembledPolynomialStorage<E>,
        _monomial_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        unreachable!("this type of gate can only be used as a main gate");
    }

    fn contribute_into_linearization(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unreachable!("this gate is indended to be the main gate and should use main gate functions")
    }
    fn contribute_into_verification_equation(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        unreachable!("this gate is indended to be the main gate and should use main gate functions")
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        Some(Self::CONSTANT_TERM_COEFF_INDEX)
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }
    fn contribute_into_linearization_commitment(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate is indended to be the main gate and should use main gate functions")
    }
}

impl<E: Engine> Gate<E> for SelectorOptimizedWidth4MainGateWithDNext {

}

impl<E: Engine> MainGate<E> for SelectorOptimizedWidth4MainGateWithDNext {
    const NUM_LINEAR_TERMS: usize = 4;
    const NUM_VARIABLES: usize = 4;
    const NUM_VARIABLES_ON_NEXT_STEP: usize = 1;

    fn range_of_multiplicative_term() -> std::ops::Range<usize> {
        4..6
    }
    fn range_of_linear_terms() -> std::ops::Range<usize> {
        0..4
    }

    fn index_for_constant_term() -> usize {
        6
    }

    fn range_of_next_step_linear_terms() -> std::ops::Range<usize> {
        7..8
    }

    fn format_term(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        assert!(instance.num_multiplicative_terms <= 1, 
            "should not use term formatting by this gate if you are using it for optimized selector with 2 multiplicative terms"
        );
        let mut flattened_variables = vec![padding; 4];
        let mut flattened_coefficients = vec![E::Fr::zero(); 8];
        let mut bitmap = SimpleBitmap::new();

        let allowed_linear = 4;
        let allowed_multiplications = 2;
        let allowed_constants = 1;

        let mut used_in_multiplication = [padding; 2];

        debug_assert!(instance.num_constant_terms <= allowed_constants, "must not containt more constants than allowed");  
        debug_assert!(instance.num_multiplicative_terms <= allowed_multiplications, "must not containt more multiplications than allowed"); 
        debug_assert!(instance.terms.len() <= allowed_constants + allowed_multiplications + allowed_linear, "gate can not fit that many terms"); 

        if instance.num_multiplicative_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Product(_, _) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Product(vars, coeff) => {
                    debug_assert_eq!(vars.len(), 2, "multiplicative terms must contain two variables");

                    flattened_variables[0] = vars[0];
                    flattened_variables[1] = vars[1];
                    used_in_multiplication[0] = vars[0];
                    used_in_multiplication[1] = vars[1];
                    flattened_coefficients[Self::AB_MULTIPLICATION_TERM_COEFF_INDEX] = coeff;
                    bitmap.set(0);
                    bitmap.set(1);
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        if instance.num_constant_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Constant(_) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Constant(coeff) => {
                    flattened_coefficients[Self::CONSTANT_TERM_COEFF_INDEX] = coeff;
                },
                _ => {
                    unreachable!("must be constant term");
                }
            }
        }

        // only additions left
        for term in instance.terms.into_iter() {
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let index = flattened_variables.iter().position(
                        |&t| t == var
                    );
                    if let Some(index) = index {
                        // there is some variable there already, so it must have come from multiplication
                        assert!(used_in_multiplication[0] == var || used_in_multiplication[1] == var,
                            "variable in linear term must only happen already if it was in multiplication");
                        flattened_coefficients[index] = coeff;
                    } else {
                        let idx = bitmap.get_next_unused();
                        flattened_variables[idx] = var;
                        flattened_coefficients[idx] = coeff;
                        bitmap.set(idx);
                    }
                },
                _ => {
                    unreachable!("must be additive term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }

    fn format_linear_term_with_duplicates(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        assert!(instance.num_multiplicative_terms <= 1, 
            "should not use term formatting by this gate if you are using it for optimized selector with 2 multiplicative terms"
        );

        let mut flattened_variables = vec![padding; 4];
        let mut flattened_coefficients = vec![E::Fr::zero(); 8];
        let mut bitmap = SimpleBitmap::new();

        let allowed_linear = 4;
        let allowed_multiplications = 0;
        let allowed_constants = 1;

        debug_assert!(instance.num_constant_terms <= allowed_constants, "must not containt more constants than allowed");  
        assert!(instance.num_multiplicative_terms <= allowed_multiplications, "must not containt multiplications"); 
        debug_assert!(instance.terms.len() <= allowed_constants + allowed_multiplications + allowed_linear, "gate can not fit that many terms"); 

        if instance.num_constant_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Constant(_) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Constant(coeff) => {
                    flattened_coefficients[Self::CONSTANT_TERM_COEFF_INDEX] = coeff;
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        for term in instance.terms.into_iter() {
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let idx = bitmap.get_next_unused();
                    flattened_variables[idx] = var;
                    flattened_coefficients[idx] = coeff;
                    bitmap.set(idx);
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }

    fn dummy_vars_to_inscribe(dummy: Variable) -> Vec<Variable> {
        vec![dummy; 4]
    }

    fn empty_coefficients() -> Vec<E::Fr> {
        vec![E::Fr::zero(); 8]
    }

    fn contribute_into_quotient_for_public_inputs<'a, 'b>(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        poly_storage: &mut AssembledPolynomialStorage<'a, E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<'b, E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
        // Include the public inputs
        let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(domain_size)?;
        for (idx, &input) in public_inputs.iter().enumerate() {
            inputs_poly.as_mut()[idx] = input;
        }
        // go into monomial form

        let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // add constants selectors vector
        let name = <Self as GateInternal<E>>::name(&self);

        let key = PolyIdentifier::GateSetupPolynomial(name, Self::CONSTANT_TERM_COEFF_INDEX);
        let constants_poly_ref = monomials_storage.get_poly(key);
        inputs_poly.add_assign(&worker, constants_poly_ref);
        drop(constants_poly_ref);

        // LDE
        let mut t_1 = inputs_poly.bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            lde_factor, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
            // skip public constants poly (was used in public inputs)
            if p == PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, Self::CONSTANT_TERM_COEFF_INDEX)) {
                continue;
            }
            ensure_in_map_or_create(&worker, 
                p, 
                domain_size, 
                omegas_bitreversed, 
                lde_factor, 
                coset_factor, 
                monomials_storage, 
                poly_storage
            )?;
        }

        let ldes_storage = &*poly_storage;

        // Q_A * A
        let q_a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            ldes_storage
        );
        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );
        let mut tmp = q_a_ref.clone();
        tmp.mul_assign(&worker, a_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_a_ref);
        drop(a_ref);

        // Q_B * B
        let q_b_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),
            ldes_storage
        );
        let b_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            ldes_storage
        );
        tmp.reuse_allocation(q_b_ref);
        tmp.mul_assign(&worker, b_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_b_ref);
        drop(b_ref);

        // // Q_C * C
        let q_c_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 2)),
            ldes_storage
        );
        let c_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            ldes_storage
        );
        tmp.reuse_allocation(q_c_ref);
        tmp.mul_assign(&worker, c_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_c_ref);
        drop(c_ref);

        // // Q_D * D
        let q_d_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 3)),
            ldes_storage
        );
        let d_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            ldes_storage
        );
        tmp.reuse_allocation(q_d_ref);
        tmp.mul_assign(&worker, d_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_d_ref);
        drop(d_ref);

        // Q_M_AB * A * B
        let q_m_ab_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, Self::AB_MULTIPLICATION_TERM_COEFF_INDEX)),
            ldes_storage
        );
        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );
        let b_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            ldes_storage
        );
        tmp.reuse_allocation(q_m_ab_ref);
        tmp.mul_assign(&worker, a_ref);
        tmp.mul_assign(&worker, b_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_m_ab_ref);
        drop(a_ref);
        drop(b_ref);

        // Q_M_AC * A * C
        let q_m_ac_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, Self::AC_MULTIPLICATION_TERM_COEFF_INDEX)),
            ldes_storage
        );
        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );
        let c_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            ldes_storage
        );
        tmp.reuse_allocation(q_m_ac_ref);
        tmp.mul_assign(&worker, a_ref);
        tmp.mul_assign(&worker, c_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_m_ac_ref);
        drop(a_ref);
        drop(c_ref);

        // Q_D_next * D_next
        let q_d_next_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 7)),
            ldes_storage
        );
        let d_next_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
            ldes_storage
        );
        tmp.reuse_allocation(q_d_next_ref);
        tmp.mul_assign(&worker, d_next_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_d_next_ref);
        drop(d_next_ref);

        t_1.scale(&worker, challenges[0]);

        Ok(t_1)
    }

    fn contribute_into_linearization_for_public_inputs(
        &self, 
        _domain_size: usize,
        _public_inputs: &[E::Fr],
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        // we actually do not depend on public inputs, but we use this form for consistency
        assert_eq!(challenges.len(), 1);

        let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
        .ok_or(SynthesisError::AssignmentMissing)?;

        let name = <Self as GateInternal<E>>::name(&self);

        // Q_a * A
        let mut result = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 0)).clone();
        result.scale(&worker, a_value);

        // Q_b * B
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 1));
        result.add_assign_scaled(&worker, poly_ref, &b_value);

        // Q_c * C
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 2));
        result.add_assign_scaled(&worker, poly_ref, &c_value);

        // Q_d * D
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 3));
        result.add_assign_scaled(&worker, poly_ref, &d_value);

        // Q_m_AB * A*B
        let mut tmp = a_value;
        tmp.mul_assign(&b_value);
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, Self::AB_MULTIPLICATION_TERM_COEFF_INDEX));
        result.add_assign_scaled(&worker, poly_ref, &tmp);

        // Q_m_AC * A*C
        let mut tmp = a_value;
        tmp.mul_assign(&c_value);
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, Self::AC_MULTIPLICATION_TERM_COEFF_INDEX));
        result.add_assign_scaled(&worker, poly_ref, &tmp);

        // Q_const
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, Self::CONSTANT_TERM_COEFF_INDEX));
        result.add_assign(&worker, poly_ref);

        // Q_dNext * D_next
        let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 7));
        result.add_assign_scaled(&worker, poly_ref, &d_next_value);

        result.scale(&worker, challenges[0]);

        Ok(result)
    }
    fn add_inputs_into_quotient(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        at: E::Fr,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        if public_inputs.len() == 0 {
            return Ok(E::Fr::zero());
        }
        assert_eq!(challenges.len(), 1);
        // just evaluate L_{i}(z) * value
        let mut contribution = E::Fr::zero();
        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64)?;
        for (idx, inp) in public_inputs.iter().enumerate() {
            let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, at)?;
            tmp.mul_assign(&inp);

            contribution.add_assign(&tmp);
        }

        contribution.mul_assign(&challenges[0]);

        Ok(contribution)
    }
    fn contribute_into_linearization_commitment_for_public_inputs<'a>(
        &self, 
        _domain_size: usize,
        _public_inputs: &[E::Fr],
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        // we actually do not depend on public inputs, but we use this form for consistency
        assert_eq!(challenges.len(), 1);

        let mut aggregate = E::G1::zero();

        let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
        .ok_or(SynthesisError::AssignmentMissing)?;
        let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
        .ok_or(SynthesisError::AssignmentMissing)?;

        let name = <Self as GateInternal<E>>::name(&self);

        // Q_a * A
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, 0)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(a_value.into_repr());
        aggregate.add_assign(&scaled);

        // Q_b * B
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, 1)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(b_value.into_repr());
        aggregate.add_assign(&scaled);

        // Q_c * C
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, 2)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(c_value.into_repr());
        aggregate.add_assign(&scaled);

        // Q_d * D
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, 3)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(d_value.into_repr());
        aggregate.add_assign(&scaled);

        // Q_m_AB * A*B
        let mut tmp = a_value;
        tmp.mul_assign(&b_value);
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, Self::AB_MULTIPLICATION_TERM_COEFF_INDEX)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(tmp.into_repr());
        aggregate.add_assign(&scaled);

        // Q_m_AC * A*B
        let mut tmp = a_value;
        tmp.mul_assign(&c_value);
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, Self::AC_MULTIPLICATION_TERM_COEFF_INDEX)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(tmp.into_repr());
        aggregate.add_assign(&scaled);

        // Q_const
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, Self::CONSTANT_TERM_COEFF_INDEX)).ok_or(SynthesisError::AssignmentMissing)?;
        aggregate.add_assign_mixed(&commitment);

        // Q_dNext * D_next
        let commitment = commitments_storage.get(&PolyIdentifier::GateSetupPolynomial(name, 7)).ok_or(SynthesisError::AssignmentMissing)?;
        let scaled = commitment.mul(d_next_value.into_repr());
        aggregate.add_assign(&scaled);

        aggregate.mul_assign(challenges[0]);

        Ok(aggregate)
    }
}