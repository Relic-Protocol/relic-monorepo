use bellman::bn256::Bn256;

use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
};

use crate::bellman::{
    SynthesisError,
};

use crate::bellman::worker::Worker;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::polynomials::*;
use crate::bellman::plonk::fft::cooley_tukey_ntt::*;

use crate::jive::{JiveEngine, JiveParams};

use crate::plonk::circuit::Assignment;

use super::allocated_num::{
    AllocatedNum,
    Num
};

#[derive(Clone, Debug, Hash, Default)]
pub struct AnemoiCustomGate;

impl<E: Engine> GateInternal<E> for AnemoiCustomGate {
    fn name(&self) -> &'static str {
        "Anemoi/Jive custom gate"
    }

    fn degree(&self) -> usize {
        3
    }

    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),

            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),

            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(0), 1),
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolyIdentifier::GateSetupPolynomial(name, 0),
            PolyIdentifier::GateSetupPolynomial(name, 1),
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
        false
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        4
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        assert!(last_row == false, "can not be applied at the last row");

        let name = <Self as GateInternal<E>>::name(&self);
        let q_const_value = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 0), row);
        let q_const2_value = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 1), row);

        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);

        let a_next_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row+1);
        let d_next_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1);

        // d - beta * a^2 = w5
        let mut w5 = a_value;
        w5.square();
        w5.mul_assign(&E::Fr::from_str("5").unwrap());
        w5.negate();
        w5.add_assign(&d_value);

        // b^3 - c = 0
        let mut tmp = b_value;
        tmp.square();
        tmp.mul_assign(&b_value);
        tmp.sub_assign(&c_value);

        if tmp.is_zero() == false {
            return tmp;
        }

        // b^2 * c - w5 = 0
        let mut tmp = b_value;
        tmp.square();
        tmp.mul_assign(&c_value);
        tmp.sub_assign(&w5);

        if tmp.is_zero() == false {
            return tmp;
        }

        // a - b = v
        // w5 + beta * v^2 + g * v + constant - d_next = 0
        let mut v = a_value;
        v.sub_assign(&b_value);
        let mut tmp = v;
        // beta
        tmp.mul_assign(&E::Fr::from_str("5").unwrap());
        // g
        tmp.add_assign(&E::Fr::from_str("5").unwrap());
        tmp.mul_assign(&v);
        tmp.add_assign(&w5);
        tmp.add_assign(&q_const_value);
        tmp.sub_assign(&d_next_value);

        if tmp.is_zero() == false {
            return tmp;
        }

        // g * d_next + v + constant_2 - a_next = 0
        let mut tmp = d_next_value;
        // g
        tmp.mul_assign(&E::Fr::from_str("5").unwrap());
        tmp.add_assign(&v);
        tmp.add_assign(&q_const2_value);
        tmp.sub_assign(&a_next_value);

        tmp
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn contribute_into_quotient(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        let name = <Self as GateInternal<E>>::name(&self);

        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
       
        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
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

        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );

        let mut tmp = a_ref.clone(); // just allocate, we don't actually use it
        drop(a_ref);

        let a_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        ).as_ref();

        let b_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            ldes_storage
        ).as_ref();

        let c_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            ldes_storage
        ).as_ref();

        let d_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            ldes_storage
        ).as_ref();

        let a_next_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(0), 1),
            ldes_storage
        ).as_ref();

        let d_next_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
            ldes_storage
        ).as_ref();

        let q_const_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            ldes_storage
        ).as_ref();

        let q_const2_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),
            ldes_storage
        ).as_ref();

        tmp.map_indexed(&worker,
            |i, el| {
                let a_value = a_raw_ref[i];
                let b_value = b_raw_ref[i];
                let c_value = c_raw_ref[i];
                let d_value = d_raw_ref[i];
                let a_next_value = a_next_raw_ref[i];
                let d_next_value = d_next_raw_ref[i];
                let q_const_value = q_const_raw_ref[i];
                let q_const2_value = q_const2_raw_ref[i];

                // d - beta * a^2 = w5
                let mut w5 = a_value;
                w5.square();
                w5.mul_assign(&E::Fr::from_str("5").unwrap());
                w5.negate();
                w5.add_assign(&d_value);

                // b^3 - c = 0
                let mut tmp = b_value;
                tmp.square();
                tmp.mul_assign(&b_value);
                tmp.sub_assign(&c_value);

                tmp.mul_assign(&challenges[0]);
                let mut result = tmp;

                // b^2 * c - w5 = 0
                let mut tmp = b_value;
                tmp.square();
                tmp.mul_assign(&c_value);
                tmp.sub_assign(&w5);

                tmp.mul_assign(&challenges[1]);
                result.add_assign(&tmp);

                // a - b = v
                let mut v = a_value;
                v.sub_assign(&b_value);
                // w5 + beta * v^2 + g * v + constant - d_next = 0
                let mut tmp = v;
                // beta
                tmp.mul_assign(&E::Fr::from_str("5").unwrap());
                // g
                tmp.add_assign(&E::Fr::from_str("5").unwrap());
                tmp.mul_assign(&v);
                tmp.add_assign(&w5);
                tmp.add_assign(&q_const_value);
                tmp.sub_assign(&d_next_value);

                tmp.mul_assign(&challenges[2]);
                result.add_assign(&tmp);

                // g * d_next + v + constant_2 - a_next = 0
                let mut tmp = d_next_value;
                // g
                tmp.mul_assign(&E::Fr::from_str("5").unwrap());
                tmp.add_assign(&v);
                tmp.add_assign(&q_const2_value);
                tmp.sub_assign(&a_next_value);

                tmp.mul_assign(&challenges[3]);
                result.add_assign(&tmp);

                *el = result;
            }, 
        );

        Ok(tmp)
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
        unreachable!("this gate does not contribute into linearization");
    }
    fn contribute_into_verification_equation(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));
        
        let name = <Self as GateInternal<E>>::name(&self);
        let q_const_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let q_const2_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)))
            .ok_or(SynthesisError::AssignmentMissing)?;

        let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
            .ok_or(SynthesisError::AssignmentMissing)?;

        let a_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(0), 1))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
            .ok_or(SynthesisError::AssignmentMissing)?;

        // d - beta * a^2 = w5
        let mut w5 = a_value;
        w5.square();
        w5.mul_assign(&E::Fr::from_str("5").unwrap());
        w5.negate();
        w5.add_assign(&d_value);

        // b^3 - c = 0
        let mut tmp = b_value;
        tmp.square();
        tmp.mul_assign(&b_value);
        tmp.sub_assign(&c_value);

        tmp.mul_assign(&challenges[0]);
        let mut result = tmp;

        // b^2 * c - w5 = 0
        let mut tmp = b_value;
        tmp.square();
        tmp.mul_assign(&c_value);
        tmp.sub_assign(&w5);

        tmp.mul_assign(&challenges[1]);
        result.add_assign(&tmp);

        // a - b = v
        let mut v = a_value;
        v.sub_assign(&b_value);
        // w5 + beta * v^2 + g * v + constant - d_next = 0
        let mut tmp = v;
        // beta
        tmp.mul_assign(&E::Fr::from_str("5").unwrap());
        // g
        tmp.add_assign(&E::Fr::from_str("5").unwrap());
        tmp.mul_assign(&v);
        tmp.add_assign(&w5);
        tmp.add_assign(&q_const_value);
        tmp.sub_assign(&d_next_value);

        tmp.mul_assign(&challenges[2]);
        result.add_assign(&tmp);

        // g * d_next + v + constant_2 - a_next = 0
        let mut tmp = d_next_value;
        // g
        tmp.mul_assign(&E::Fr::from_str("5").unwrap());
        tmp.add_assign(&v);
        tmp.add_assign(&q_const2_value);
        tmp.sub_assign(&a_next_value);

        tmp.mul_assign(&challenges[3]);
        result.add_assign(&tmp);

        Ok(result)
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }

    fn contribute_into_linearization_commitment(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        _challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
}

impl<E: Engine> Gate<E> for AnemoiCustomGate {}

pub fn jive_2_1<E: JiveEngine, CS: ConstraintSystem<E>>(cs: &mut CS, x: &AllocatedNum<E>, y: &AllocatedNum<E>, params: &E::Params) -> Result<AllocatedNum<E>, SynthesisError>
{
    let C: Vec<_> = E::ROUND_CONSTANTS_C.iter().map(|s| E::Fr::from_str(s).unwrap()).collect();
    let D: Vec<_> = E::ROUND_CONSTANTS_D.iter().map(|s| E::Fr::from_str(s).unwrap()).collect();
    let g = E::Fr::from_str("5").unwrap();
    // g**-1
    let delta = E::Fr::from_str(E::DELTA).unwrap();
    let beta = g;

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let before = cs.get_current_step_number();

    // Initial constants + linear layer
    // u = x + y * g + d * g + c
    let mut constant = D[0];
    constant.mul_assign(&g);
    constant.add_assign(&C[0]);
    let mut u = AllocatedNum::<E>::alloc(
        cs,
        || {
            let x = *x.get_value().get()?;
            let y = *y.get_value().get()?;
            let mut result = D[0];
            result.add_assign(&y);
            result.mul_assign(&g);
            result.add_assign(&C[0]);
            result.add_assign(&x);
            Ok(result)
        }
    )?;
    let mut term = MainGateTerm::<E>::new();
    term.add_assign(
        ArithmeticTerm::from_variable(x.get_variable())
    );
    term.add_assign(
        ArithmeticTerm::from_variable_and_coeff(y.get_variable(), g)
    );
    term.add_assign(
        ArithmeticTerm::constant(constant)
    );
    term.sub_assign(
        ArithmeticTerm::from_variable(u.get_variable())
    );
    cs.allocate_main_gate(term)?;

    // v = u * g + y + d
    let mut v = AllocatedNum::<E>::alloc(
        cs,
        || {
            let u = *u.get_value().get()?;
            let y = *y.get_value().get()?;
            let mut result = g;
            result.mul_assign(&u);
            result.add_assign(&y);
            result.add_assign(&D[0]);
            Ok(result)
        }
    )?;
    let mut term = MainGateTerm::<E>::new();
    term.add_assign(
        ArithmeticTerm::from_variable(y.get_variable())
    );
    term.add_assign(
        ArithmeticTerm::from_variable_and_coeff(u.get_variable(), g)
    );
    term.add_assign(
        ArithmeticTerm::constant(D[0])
    );
    term.sub_assign(
        ArithmeticTerm::from_variable(v.get_variable())
    );
    cs.allocate_main_gate(term)?;

    for n in 0..19 {
        if params.use_custom_gate() {
            let w = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let u = *u.get_value().get()?;
                    let v = *v.get_value().get()?;
                    let mut w5 = v;
                    w5.square();
                    w5.mul_assign(&beta);
                    w5.negate();
                    w5.add_assign(&u);
                    let result = w5.pow(&E::Fr::from_str(E::ALPHA_INV).unwrap().into_repr());

                    Ok(result)
                }
            )?;
            // # Custom gate
            // # A = y
            // # B = w
            // # C = w**3
            // # D = x
            // # Anext = v'
            // # Dnext = u'
            // #
            // # w5 = D - A*A
            // # B*B*B - C = 0
            // # B*B*C - w5 = 0
            // # v = A - B
            // # w5 + (beta * v + g) * v + const - Dnext = 0
            // # g * Dnext + v + const2 - Anext = 0
            // const = delta + c + d * g
            // u' = w5 + beta * (v*v) + v * g + const
            // const = d
            // v' = u' * g + initial_v - w + const
            let initial_v = v;

            let third = AllocatedNum::alloc(
                cs, 
                || {
                    let w = *w.get_value().get()?;
                    let mut tmp = w;
                    tmp.square();
                    tmp.mul_assign(&w);

                    Ok(tmp)
                }
            )?;

            // const = delta + c + d * g
            // up = w5 + beta * (v*v) + v * g + const
            let mut constant = D[n+1];
            constant.mul_assign(&g);
            constant.add_assign(&C[n+1]);
            constant.add_assign(&delta);

            cs.new_single_gate_for_trace_step(
                &AnemoiCustomGate::default(),
                &[constant, D[n+1]],
                &[initial_v.get_variable(), w.get_variable(), third.get_variable(), u.get_variable()],
                &[]
            )?;

            // constrained as part of the previous and next gate
            u = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let w = *w.get_value().get()?;
                    let mut v = *initial_v.get_value().get()?;
                    v.sub_assign(&w);
                    let w5 = w.pow(&[5u64]);
                    let mut tmp = v;
                    tmp.square();
                    tmp.mul_assign(&beta);
                    let mut result = D[n+1];
                    result.add_assign(&v);
                    result.mul_assign(&g);
                    result.add_assign(&C[n+1]);
                    result.add_assign(&delta);
                    result.add_assign(&w5);
                    result.add_assign(&tmp);
                    Ok(result)
                }
            )?;
            v = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let v = *initial_v.get_value().get()?;
                    let u = *u.get_value().get()?;
                    let w = *w.get_value().get()?;
                    let mut result = u;
                    result.mul_assign(&g);
                    result.add_assign(&D[n+1]);
                    result.add_assign(&v);
                    result.sub_assign(&w);
                    Ok(result)
                }
            )?;
        } else {
            // w5 = x - beta * (y*y)
            // w = w5 ** alpha_inv
            // v = y - w
            let w5 = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let u = *u.get_value().get()?;
                    let v = *v.get_value().get()?;
                    let mut result = v;
                    result.square();
                    result.mul_assign(&beta);
                    result.negate();
                    result.add_assign(&u);
                    Ok(result)
                }
            )?;
            let w = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let w5 = *w5.get_value().get()?;
                    let result = w5.pow(&E::Fr::from_str(E::ALPHA_INV).unwrap().into_repr());

                    Ok(result)
                }
            )?;
            let mut term = MainGateTerm::<E>::new();
            term.sub_assign(
                ArithmeticTerm::from_variable_and_coeff(v.get_variable(), beta).mul_by_variable(v.get_variable())
            );
            term.add_assign(
                ArithmeticTerm::from_variable(u.get_variable())
            );
            term.sub_assign(
                ArithmeticTerm::from_variable(w5.get_variable())
            );
            cs.allocate_main_gate(term)?;

            // we take a value and make 5th power from it
            let square = w.square(cs)?;
            let quad = square.square(cs)?;

            let mut term = MainGateTerm::<E>::new();
            let fifth_term = ArithmeticTerm::from_variable(quad.get_variable()).mul_by_variable(w.get_variable());
            let w5_term = ArithmeticTerm::from_variable(w5.get_variable());
            term.add_assign(fifth_term);
            term.sub_assign(w5_term);
            cs.allocate_main_gate(term)?;

            v = v.sub(cs, &w)?;

            // const = delta + c + d * g
            // up = w5 + beta * (v*v) + v * g + const
            let mut constant = D[n+1];
            constant.mul_assign(&g);
            constant.add_assign(&C[n+1]);
            constant.add_assign(&delta);
            u = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let v = *v.get_value().get()?;
                    let w5 = *w5.get_value().get()?;
                    let mut tmp = v;
                    tmp.square();
                    tmp.mul_assign(&beta);
                    let mut result = D[n+1];
                    result.add_assign(&v);
                    result.mul_assign(&g);
                    result.add_assign(&C[n+1]);
                    result.add_assign(&delta);
                    result.add_assign(&w5);
                    result.add_assign(&tmp);
                    Ok(result)
                }
            )?;
            // Custom gate requires specific assignments
            //  A = v
            //  B = v
            //  C = u'
            //  D = w5
            cs.new_single_gate_for_trace_step(
                &CS::MainGate::default(),
                &[g, E::Fr::zero(), minus_one, E::Fr::one(), beta, constant, E::Fr::zero()],
                &[v.get_variable(), v.get_variable(), u.get_variable(), w5.get_variable()],
                &[]
            )?;
            // const = d
            // v' = u' * g + v + const
            let prev_v = v;
            v = AllocatedNum::<E>::alloc(
                cs,
                || {
                    let v = *prev_v.get_value().get()?;
                    let u = *u.get_value().get()?;
                    let mut result = u;
                    result.mul_assign(&g);
                    result.add_assign(&D[n+1]);
                    result.add_assign(&v);
                    Ok(result)
                }
            )?;
            cs.new_single_gate_for_trace_step(
                &CS::MainGate::default(),
                &[E::Fr::one(), g, minus_one, E::Fr::zero(), E::Fr::zero(), D[n+1], E::Fr::zero()],
                &[prev_v.get_variable(), u.get_variable(), v.get_variable(), w5.get_variable()],
                &[]
            )?;
        }

    }

    let partial_result = AllocatedNum::<E>::alloc(
        cs,
        || {
            let u = *u.get_value().get()?;
            let v = *v.get_value().get()?;
            let x = *x.get_value().get()?;
            let mut result = u;
            result.add_assign(&v);
            result.add_assign(&x);
            Ok(result)
        }
    )?;
    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(),
        &[E::Fr::one(), E::Fr::one(), minus_one, E::Fr::one(), E::Fr::zero(), E::Fr::zero(), E::Fr::zero()],
        &[v.get_variable(), x.get_variable(), partial_result.get_variable(), u.get_variable()],
        &[]
    )?;

    let result = partial_result.add(cs, &y)?;
    Ok(result)
}

#[cfg(test)]
mod test {
    use super::*;
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use crate::bellman::plonk::better_better_cs::cs::{
        TrivialAssembly, 
        PlonkCsWidth4WithNextStepParams, 
        Width4MainGateWithDNext
    };

    use crate::plonk::circuit::Width4WithCustomGates;

    const TEST_VECTORS: &[(&str, &str, &str)] = &[
        ("0", "0", "1336634770235204994463052552258872349785679500588840713630535706829152762711"),
        ("1", "1", "2009653109573343791671598177058821500782170642108037528421009262312308017560"),
        ("0", "1", "15242464356090922040755695424099718922649203940346730555264324305750364514407"),
        ("1", "0", "19690920424780417357962140192170211143156945507421957802696673695925821847577"),
        ("21288111031067976839871433651188571929936899212691149038613494677346172987633", "15477392567216137557784875118934447396037328872060187695434788571817406298171", "14139897374621145183138528864971459499158788476854743679377086403402283004105"),
    ];

    struct TestJiveCircuit<E: JiveEngine> {
        params: E::Params,
        x: E::Fr,
        y: E::Fr,
        result: E::Fr,
    }

    impl<E: JiveEngine> Circuit<E> for TestJiveCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                    AnemoiCustomGate::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> 
        {
            let x = AllocatedNum::alloc(cs, || Ok(self.x))?;
            let y = AllocatedNum::alloc(cs, || Ok(self.y))?;
            let result = jive_2_1(cs, &x, &y, &self.params)?;
            assert_eq!(result.get_value().unwrap(), self.result);

            Ok(())
        }
    }

    #[test]
    fn test_jive_2_1() {
        use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
        use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
        use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
        use crate::bellman::plonk::better_better_cs::verifier::verify;
        let worker = Worker::new();
        let crs = Crs::<Bn256, CrsForMonomialForm>::dummy_crs(1 << 20);
        for (x_str, y_str, result_str) in TEST_VECTORS.iter() {
            //let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            let circuit = TestJiveCircuit {
                params: Bn256JiveParams::new(true),
                x: Fr::from_str(x_str).unwrap(),
                y: Fr::from_str(y_str).unwrap(),
                result: Fr::from_str(result_str).unwrap(),
            };

            let mut assembly = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
            circuit.synthesize(&mut assembly).expect("must work");
            assembly.finalize();
            assert!(assembly.is_satisfied());

            let setup = assembly.create_setup::<TestJiveCircuit::<Bn256>>(&worker).unwrap();
            let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();

            let proof = assembly
                .create_proof::<_, RollingKeccakTranscript<Fr>>(&worker, &setup, &crs, None)
                .unwrap();

            let valid = verify::<_, _, RollingKeccakTranscript<Fr>>(&vk, &proof, None).unwrap();
            assert!(valid);    
        }
    }
}
