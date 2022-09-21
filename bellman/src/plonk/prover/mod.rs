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


#[derive(Debug)]
struct ProvingAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E>>,
    aux_gates: Vec<Gate<E>>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    inputs_map: Vec<usize>,

    is_finalized: bool
}

impl<E: Engine> ConstraintSystem<E> for ProvingAssembly<E> {
    const ZERO: Variable = Variable(Index::Aux(1));
    const ONE: Variable = Variable(Index::Aux(2));

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

        let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(E::Fr::zero()), self.dummy_variable());
        // let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(value), self.dummy_variable());
        self.input_gates.push(gate);

        Ok(input_var)

    }

    // enforce variable as boolean
    fn enforce_boolean(&mut self, variable: Variable) -> Result<(), SynthesisError> {
        let gate = Gate::<E>::new_enforce_boolean_gate(variable, self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate an abstract gate
    fn new_gate<F>(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr, E::Fr, E::Fr), values: F) -> Result<(), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr), SynthesisError>
    {
        unimplemented!()
    }

    // allocate a constant
    fn enforce_constant(&mut self, variable: Variable, constant: E::Fr) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a multiplication gate
    fn enforce_mul_2(&mut self, variables: (Variable, Variable)) -> Result<(), SynthesisError> {
        // q_l, q_r, q_o, q_c = 0, q_m = 1
        let (v_0, v_1) = variables;
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        let gate = Gate::<E>::new_gate((v_0, v_1, self.dummy_variable()), (zero, zero, zero, one, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a multiplication gate
    fn enforce_mul_3(&mut self, variables: (Variable, Variable, Variable)) -> Result<(), SynthesisError> {
        let gate = Gate::<E>::new_multiplication_gate(variables);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a linear combination gate
    fn enforce_zero_2(&mut self, variables: (Variable, Variable), coeffs:(E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let (v_0, v_1) = variables;
        let (c_0, c_1) = coeffs;
        let zero = E::Fr::zero();

        let gate = Gate::<E>::new_gate((v_0, v_1, self.dummy_variable()), (c_0, c_1, zero, zero, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a linear combination gate
    fn enforce_zero_3(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E>::new_enforce_zero_gate(variables, coeffs);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
        
    }
}

impl<E: Engine> ProvingAssembly<E> {
    fn new_empty_gate(&mut self) -> usize {
        self.n += 1;
        let index = self.n;

        self.aux_gates.push(Gate::<E>::empty());

        index
    }

    fn set_gate(&mut self, gate: Gate<E>, index: usize) {
        self.aux_gates[index-1] = gate;
    }

    pub(crate) fn new() -> Self {
        let mut tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            inputs_map: vec![],

            is_finalized: false,
        };

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        let one = tmp.alloc(|| Ok(E::Fr::one())).expect("should have no issues");
        tmp.enforce_constant(one, E::Fr::one()).expect("should have no issues");

        match (zero, <Self as ConstraintSystem<E>>::ZERO) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        match (one, <Self as ConstraintSystem<E>>::ONE) {
            (Variable(Index::Aux(2)), Variable(Index::Aux(2))) => {},
            _ => panic!("one variable is incorrect")
        }

        match (tmp.dummy_variable(), <Self as ConstraintSystem<E>>::ZERO) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        <Self as ConstraintSystem<E>>::ZERO
        // Variable(Index::Aux(0))
    }

    pub(crate) fn make_wire_assingments(&self) -> (Vec<E::Fr>, Vec<E::Fr>, Vec<E::Fr>) {
        assert!(self.is_finalized);
        // create a vector of gate assingments
        // if a_i = j then w_j = f_l(g^i)

        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut f_l = vec![E::Fr::zero(); total_num_gates];
        let mut f_r = vec![E::Fr::zero(); total_num_gates];
        let mut f_o = vec![E::Fr::zero(); total_num_gates];

        for (i, gate) in self.input_gates.iter().chain(&self.aux_gates).enumerate()
        {
            match gate.a_wire() {
                Variable(Index::Input(index)) => {
                    f_l[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_l[i] = self.aux_assingments[index - 1];
                },
            }

            match gate.b_wire() {
                Variable(Index::Input(index)) => {
                    f_r[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_r[i] = self.aux_assingments[index - 1];
                },
            }

            match gate.c_wire() {
                Variable(Index::Input(index)) => {
                    f_o[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_o[i] = self.aux_assingments[index - 1];
                },
            }
        }

        (f_l, f_r, f_o)
    }

    pub(crate) fn make_circuit_description_polynomials(&self, worker: &Worker) -> Result<(
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>,
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>
    ), SynthesisError> {
        assert!(self.is_finalized);

        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_l = vec![E::Fr::zero(); total_num_gates];
        let mut q_r = vec![E::Fr::zero(); total_num_gates];
        let mut q_o = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];

        fn coeff_into_field_element<E: Engine>(coeff: & Coeff<E>) -> E::Fr {
            match coeff {
                Coeff::Zero => {
                    E::Fr::zero()
                },
                Coeff::One => {
                    E::Fr::one()
                },
                Coeff::NegativeOne => {
                    let mut tmp = E::Fr::one();
                    tmp.negate();

                    tmp
                },
                Coeff::Full(c) => {
                    *c
                },
            }
        }

        // expect a small number of inputs
        for (((((gate, q_l), q_r), q_o), q_m), q_c) in self.input_gates.iter()
                                            .zip(q_l.iter_mut())
                                            .zip(q_r.iter_mut())
                                            .zip(q_o.iter_mut())
                                            .zip(q_m.iter_mut())
                                            .zip(q_c.iter_mut())
        {
            *q_l = coeff_into_field_element(&gate.q_l);
            *q_r = coeff_into_field_element(&gate.q_r);
            *q_o = coeff_into_field_element(&gate.q_o);
            *q_m = coeff_into_field_element(&gate.q_m);
            *q_c = coeff_into_field_element(&gate.q_c);
        }


        let num_input_gates = self.input_gates.len();
        let q_l_aux = &mut q_l[num_input_gates..];
        let q_r_aux = &mut q_r[num_input_gates..];
        let q_o_aux = &mut q_o[num_input_gates..];
        let q_m_aux = &mut q_m[num_input_gates..];
        let q_c_aux = &mut q_c[num_input_gates..];

        debug_assert!(self.aux_gates.len() == q_l_aux.len());

        worker.scope(self.aux_gates.len(), |scope, chunk| {
            for (((((gate, q_l), q_r), q_o), q_m), q_c) in self.aux_gates.chunks(chunk)
                                                            .zip(q_l_aux.chunks_mut(chunk))
                                                            .zip(q_r_aux.chunks_mut(chunk))
                                                            .zip(q_o_aux.chunks_mut(chunk))
                                                            .zip(q_m_aux.chunks_mut(chunk))
                                                            .zip(q_c_aux.chunks_mut(chunk))
            {
                scope.spawn(move |_| {
                    for (((((gate, q_l), q_r), q_o), q_m), q_c) in gate.iter()
                                                            .zip(q_l.iter_mut())
                                                            .zip(q_r.iter_mut())
                                                            .zip(q_o.iter_mut())
                                                            .zip(q_m.iter_mut())
                                                            .zip(q_c.iter_mut())
                        {
                            *q_l = coeff_into_field_element(&gate.q_l);
                            *q_r = coeff_into_field_element(&gate.q_r);
                            *q_o = coeff_into_field_element(&gate.q_o);
                            *q_m = coeff_into_field_element(&gate.q_m);
                            *q_c = coeff_into_field_element(&gate.q_c);
                        }
                });
            }
        });

        let q_l = Polynomial::from_values(q_l)?;
        let q_r = Polynomial::from_values(q_r)?;
        let q_o = Polynomial::from_values(q_o)?;
        let q_m = Polynomial::from_values(q_m)?;
        let q_c = Polynomial::from_values(q_c)?;

        Ok((q_l, q_r, q_o, q_m, q_c))
    }

    pub(crate) fn calculate_permutations_as_in_a_paper(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        assert!(self.is_finalized);

        let num_gates = self.input_gates.len() + self.aux_gates.len();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        for (j, gate) in self.input_gates.iter().chain(&self.aux_gates).enumerate()
        {
            match gate.a_wire() {
                Variable(Index::Input(index)) => {
                    let i = *index;
                    partitions[i].push(j+1);
                },
                Variable(Index::Aux(index)) => {
                    if *index != 0 {
                        let i = index + num_inputs;
                        partitions[i].push(j+1);
                    }
                },
            }

            match gate.b_wire() {
                Variable(Index::Input(index)) => {
                    let i = *index;
                    partitions[i].push(j + 1 + num_gates);
                },
                Variable(Index::Aux(index)) => {
                    if *index != 0 {
                        let i = index + num_inputs;
                        partitions[i].push(j + 1 + num_gates);
                    }
                },
            }

            match gate.c_wire() {
                Variable(Index::Input(index)) => {
                    let i = *index;
                    partitions[i].push(j + 1 + 2*num_gates);
                },
                Variable(Index::Aux(index)) => {
                    if *index != 0 {
                        let i = index + num_inputs;
                        partitions[i].push(j + 1 + 2*num_gates);
                    }
                },
            }
        }

        let mut sigma_1: Vec<_> = (1..=num_gates).collect();
        let mut sigma_2: Vec<_> = ((num_gates+1)..=(2*num_gates)).collect();
        let mut sigma_3: Vec<_> = ((2*num_gates + 1)..=(3*num_gates)).collect();

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate(mut vec: Vec<usize>) -> Vec<usize> {
            if vec.len() > 0 {
                let els: Vec<_> = vec.drain(0..1).collect();
                vec.push(els[0]);
            }

            vec
        }

        for (i, partition) in partitions.into_iter().enumerate().skip(1) {
            // copy-permutation should have a cycle around the partition

            let permutation = rotate(partition.clone());
            permutations[i] = permutation.clone();

            for (original, new) in partition.into_iter()
                                    .zip(permutation.into_iter()) 
            {
                if original <= num_gates {
                    debug_assert!(sigma_1[original - 1] == original);
                    sigma_1[original - 1] = new;
                } else if original <= 2*num_gates {
                    debug_assert!(sigma_2[original - num_gates - 1] == original);
                    sigma_2[original - num_gates - 1] = new;
                } else {
                    debug_assert!(sigma_3[original - 2*num_gates - 1] == original);
                    sigma_3[original - 2*num_gates - 1] = new;
                }
            }
        }

        (sigma_1, sigma_2, sigma_3)
    }

    fn make_s_id(&self) -> Vec<usize> {
        let size = self.input_gates.len() + self.aux_gates.len();
        let result: Vec<_> = (1..=size).collect();

        result
    }

    pub(crate) fn output_setup_polynomials(&self, worker: &Worker) -> Result<
    (
        Polynomial::<E::Fr, Coefficients>, // q_l
        Polynomial::<E::Fr, Coefficients>, // q_r
        Polynomial::<E::Fr, Coefficients>, // q_o
        Polynomial::<E::Fr, Coefficients>, // q_m
        Polynomial::<E::Fr, Coefficients>, // q_c
        Polynomial::<E::Fr, Coefficients>, // s_id
        Polynomial::<E::Fr, Coefficients>, // sigma_1
        Polynomial::<E::Fr, Coefficients>, // sigma_2
        Polynomial::<E::Fr, Coefficients>, // sigma_3
    ), SynthesisError> 
    {
        assert!(self.is_finalized);

        let s_id = self.make_s_id();
        let (sigma_1, sigma_2, sigma_3) = self.calculate_permutations_as_in_a_paper();

        let s_id = convert_to_field_elements::<E::Fr>(&s_id, &worker);
        let sigma_1 = convert_to_field_elements::<E::Fr>(&sigma_1, &worker);
        let sigma_2 = convert_to_field_elements::<E::Fr>(&sigma_2, &worker);
        let sigma_3 = convert_to_field_elements::<E::Fr>(&sigma_3, &worker);

        let s_id = Polynomial::from_values(s_id)?;
        let sigma_1 = Polynomial::from_values(sigma_1)?;
        let sigma_2 = Polynomial::from_values(sigma_2)?;
        let sigma_3 = Polynomial::from_values(sigma_3)?;

        let (q_l, q_r, q_o, q_m, q_c) = self.make_circuit_description_polynomials(&worker)?;

        let s_id = s_id.ifft(&worker);
        let sigma_1 = sigma_1.ifft(&worker);
        let sigma_2 = sigma_2.ifft(&worker);
        let sigma_3 = sigma_3.ifft(&worker);

        let q_l = q_l.ifft(&worker);
        let q_r = q_r.ifft(&worker);
        let q_o = q_o.ifft(&worker);
        let q_m = q_m.ifft(&worker);
        let q_c = q_c.ifft(&worker);

        Ok((q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3))
    }

    pub(crate) fn num_gates(&self) -> usize {
        assert!(self.is_finalized);

        self.input_gates.len() + self.aux_gates.len()
    }

    fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }
        let n = self.input_gates.len() + self.aux_gates.len();
        if (n+1).is_power_of_two() {
            return;
        }

        let empty_gate = Gate::<E>::new_empty_gate(self.dummy_variable());

        let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();

        self.aux_gates.resize(new_aux_len, empty_gate);

        self.is_finalized = true;
    }

    fn calculate_inverse_vanishing_polynomial_in_a_coset(&self, worker: &Worker, poly_size:usize, vahisning_size: usize) -> Result<Polynomial::<E::Fr, Values>, SynthesisError> {
        assert!(poly_size.is_power_of_two());
        assert!(vahisning_size.is_power_of_two());

        // update from the paper - it should not hold for the last generator, omega^(n) in original notations

        // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

        let domain = Domain::<E::Fr>::new_for_size(vahisning_size as u64)?;
        let n_domain_omega = domain.generator;
        let mut root = n_domain_omega.pow([(vahisning_size - 1) as u64]);
        root.negate();

        let multiplicative_generator = E::Fr::multiplicative_generator();

        let mut negative_one = E::Fr::one();
        negative_one.negate();

        let mut numerator = Polynomial::<E::Fr, Values>::from_values(vec![multiplicative_generator; poly_size])?;
        // evaluate X in linear time

        numerator.distribute_powers(&worker, numerator.omega);
        numerator.add_constant(&worker, &root);

        // numerator.add_constant(&worker, &negative_one);
        // now it's a series of values in a coset

        // now we should evaluate X^(n+1) - 1 in a linear time

        let shift = multiplicative_generator.pow([vahisning_size as u64]);
        
        let mut denominator = Polynomial::<E::Fr, Values>::from_values(vec![shift; poly_size])?;

        // elements are h^size - 1, (hg)^size - 1, (hg^2)^size - 1, ...

        denominator.distribute_powers(&worker, denominator.omega.pow([vahisning_size as u64]));
        denominator.add_constant(&worker, &negative_one);

        denominator.batch_inversion(&worker)?;

        numerator.mul_assign(&worker, &denominator);

        Ok(numerator)
    }

    fn evaluate_inverse_vanishing_poly(&self, vahisning_size: usize, point: E::Fr) -> E::Fr {
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

    fn calculate_lagrange_poly(&self, worker: &Worker, poly_size:usize, poly_number: usize) -> Result<Polynomial::<E::Fr, Coefficients>, SynthesisError> {
        assert!(poly_size.is_power_of_two());
        assert!(poly_number < poly_size);

        let mut poly = Polynomial::<E::Fr, Values>::from_values(vec![E::Fr::zero(); poly_size])?;

        poly.as_mut()[poly_number] = E::Fr::one();

        Ok(poly.ifft(&worker))
    }
}


// for a non-homomorphic case we do not need r(x) polynomial at all, just open all the parts of t(x) at z

pub struct PlonkNonhomomorphicProof<E: Engine, S: CommitmentScheme<E::Fr> >{
    pub a_opening_value: E::Fr,
    pub b_opening_value: E::Fr,
    pub c_opening_value: E::Fr,
    pub q_l_opening_value: E::Fr,
    pub q_r_opening_value: E::Fr,
    pub q_o_opening_value: E::Fr,
    pub q_m_opening_value: E::Fr,
    pub q_c_opening_value: E::Fr,
    pub s_id_opening_value: E::Fr,
    pub sigma_1_opening_value: E::Fr,
    pub sigma_2_opening_value: E::Fr,
    pub sigma_3_opening_value: E::Fr,
    pub z_1_unshifted_opening_value: E::Fr,
    pub z_2_unshifted_opening_value: E::Fr,
    pub z_1_shifted_opening_value: E::Fr,
    pub z_2_shifted_opening_value: E::Fr,
    pub t_opening_value: E::Fr,
    pub a_commitment: S::Commitment,
    pub b_commitment: S::Commitment,
    pub c_commitment: S::Commitment,
    pub z_1_commitment: S::Commitment,
    pub z_2_commitment: S::Commitment,
    pub t_commitment: S::Commitment,
    pub openings_proof: S::OpeningProof,
    // pub shifted_openings_proof: S::OpeningProof,
    pub t_opening_proof: S::OpeningProof,
}

pub struct PlonkChunkedNonhomomorphicProof<E: Engine, S: CommitmentScheme<E::Fr> >{
    pub a_opening_value: E::Fr,
    pub b_opening_value: E::Fr,
    pub c_opening_value: E::Fr,
    pub q_l_opening_value: E::Fr,
    pub q_r_opening_value: E::Fr,
    pub q_o_opening_value: E::Fr,
    pub q_m_opening_value: E::Fr,
    pub q_c_opening_value: E::Fr,
    pub s_id_opening_value: E::Fr,
    pub sigma_1_opening_value: E::Fr,
    pub sigma_2_opening_value: E::Fr,
    pub sigma_3_opening_value: E::Fr,
    pub z_1_unshifted_opening_value: E::Fr,
    pub z_2_unshifted_opening_value: E::Fr,
    pub z_1_shifted_opening_value: E::Fr,
    pub z_2_shifted_opening_value: E::Fr,
    pub t_low_opening_value: E::Fr,
    pub t_mid_opening_value: E::Fr,
    pub t_high_opening_value: E::Fr,
    pub a_commitment: S::Commitment,
    pub b_commitment: S::Commitment,
    pub c_commitment: S::Commitment,
    pub z_1_commitment: S::Commitment,
    pub z_2_commitment: S::Commitment,
    pub t_low_commitment: S::Commitment,
    pub t_mid_commitment: S::Commitment,
    pub t_high_commitment: S::Commitment,
    pub openings_proof: S::OpeningProof,
}

pub fn prove_nonhomomorphic<E: Engine, S: CommitmentScheme<E::Fr, Prng = T>, T: Transcript<E::Fr, Input = S::Commitment>, C: Circuit<E>>(
    circuit: &C, 
    setup: &PlonkSetup<E, S>,
    aux: &PlonkSetupAuxData<E, S>,
    meta: S::Meta,
    large_meta: S::Meta
) -> Result<PlonkNonhomomorphicProof<E, S>, SynthesisError> {
    assert!(S::IS_HOMOMORPHIC == false);

    let mut assembly = ProvingAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.num_gates();

    let committer = S::new_for_size(num_gates.next_power_of_two(), meta);
    let large_committer = S::new_for_size(4 * num_gates.next_power_of_two(), large_meta);

    let worker = Worker::new();

    let mut transcript = T::new();

    let n = assembly.input_gates.len() + assembly.aux_gates.len();

    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = n + 1;
    assert!(required_domain_size.is_power_of_two());

    println!("Start work with polynomials");

    let (w_l, w_r, w_o) = assembly.make_wire_assingments();

    let w_l = Polynomial::<E::Fr, Values>::from_values_unpadded(w_l)?;
    let w_r = Polynomial::<E::Fr, Values>::from_values_unpadded(w_r)?;
    let w_o = Polynomial::<E::Fr, Values>::from_values_unpadded(w_o)?;

    let a_poly = w_l.clone_padded_to_domain()?.ifft(&worker);
    let b_poly = w_r.clone_padded_to_domain()?.ifft(&worker);
    let c_poly = w_o.clone_padded_to_domain()?.ifft(&worker);

    let (a_commitment, a_aux_data) = committer.commit_single(&a_poly);
    let (b_commitment, b_aux_data) = committer.commit_single(&b_poly);
    let (c_commitment, c_aux_data) = committer.commit_single(&c_poly);

    transcript.commit_input(&a_commitment);
    transcript.commit_input(&b_commitment);
    transcript.commit_input(&c_commitment);

    // TODO: Add public inputs

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    let mut w_l_plus_gamma = w_l.clone();
    w_l_plus_gamma.add_constant(&worker, &gamma);

    let mut w_r_plus_gamma = w_r.clone();
    w_r_plus_gamma.add_constant(&worker, &gamma);

    let mut w_o_plus_gamma = w_o.clone();
    w_o_plus_gamma.add_constant(&worker, &gamma);

    let z_1 = {
        let n = assembly.input_gates.len() + assembly.aux_gates.len();
        let s_id_1: Vec<_> = (1..=n).collect();
        let s_id_1 = convert_to_field_elements(&s_id_1, &worker);
        let s_id_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &s_id_1, &beta);
        drop(s_id_1);

        let s_id_2: Vec<_> = ((n+1)..=(2*n)).collect();
        let s_id_2 = convert_to_field_elements(&s_id_2, &worker);
        let s_id_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &s_id_2, &beta);
        drop(s_id_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let s_id_3: Vec<_> = ((2*n+1)..=(3*n)).collect();
        let s_id_3 = convert_to_field_elements(&s_id_3, &worker);
        let s_id_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &s_id_3, &beta);
        drop(s_id_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        Polynomial::<E::Fr, Values>::from_values(prepadded)?
    };

    let z_2 = {
        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();

        let sigma_1 = convert_to_field_elements(&sigma_1, &worker);
        let sigma_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &sigma_1, &beta);
        drop(sigma_1);

        let sigma_2 = convert_to_field_elements(&sigma_2, &worker);
        let sigma_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &sigma_2, &beta);
        drop(sigma_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let sigma_3 = convert_to_field_elements(&sigma_3, &worker);
        let sigma_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &sigma_3, &beta);
        drop(sigma_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        let z_2 = Polynomial::<E::Fr, Values>::from_values(prepadded)?;

        z_2
    };

    let z_1 = z_1.ifft(&worker);
    let z_2 = z_2.ifft(&worker);

    let (z_1_commitment, z_1_aux) = committer.commit_single(&z_1);
    let (z_2_commitment, z_2_aux) = committer.commit_single(&z_2);

    transcript.commit_input(&z_1_commitment);
    transcript.commit_input(&z_2_commitment);

    let mut z_1_shifted = z_1.clone();
    z_1_shifted.distribute_powers(&worker, z_1.omega);
    
    let mut z_2_shifted = z_2.clone();
    z_2_shifted.distribute_powers(&worker, z_2.omega);
    
    let a_lde = a_poly.clone().coset_lde(&worker, 4)?;
    let b_lde = b_poly.clone().coset_lde(&worker, 4)?;
    let c_lde = c_poly.clone().coset_lde(&worker, 4)?;

    let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = assembly.output_setup_polynomials(&worker)?;

    let q_l_lde = q_l.clone().coset_lde(&worker, 4)?;
    let q_r_lde = q_r.clone().coset_lde(&worker, 4)?;
    let q_o_lde = q_o.clone().coset_lde(&worker, 4)?;
    let q_m_lde = q_m.clone().coset_lde(&worker, 4)?;
    let q_c_lde = q_c.clone().coset_lde(&worker, 4)?;
    let s_id_lde = s_id.clone().coset_lde(&worker, 4)?;
    let sigma_1_lde = sigma_1.clone().coset_lde(&worker, 4)?;
    let sigma_2_lde = sigma_2.clone().coset_lde(&worker, 4)?;
    let sigma_3_lde = sigma_3.clone().coset_lde(&worker, 4)?;

    // we do not commit those cause those are known already

    let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    let alpha = transcript.get_challenge();

    let mut vanishing_poly_inverse = assembly.calculate_inverse_vanishing_polynomial_in_a_coset(&worker, q_c_lde.size(), required_domain_size.next_power_of_two())?;

    let mut t_1 = {
        let mut t_1 = q_c_lde;

        let mut q_l_by_a = q_l_lde;
        q_l_by_a.mul_assign(&worker, &a_lde);
        t_1.add_assign(&worker, &q_l_by_a);
        drop(q_l_by_a);

        let mut q_r_by_b = q_r_lde;
        q_r_by_b.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_r_by_b);
        drop(q_r_by_b);

        let mut q_o_by_c = q_o_lde;
        q_o_by_c.mul_assign(&worker, &c_lde);
        t_1.add_assign(&worker, &q_o_by_c);
        drop(q_o_by_c);

        let mut q_m_by_ab = q_m_lde;
        q_m_by_ab.mul_assign(&worker, &a_lde);
        q_m_by_ab.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_m_by_ab);
        drop(q_m_by_ab);

        vanishing_poly_inverse.scale(&worker, alpha);

        t_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1
    };

    let z_1_lde = z_1.clone().coset_lde(&worker, 4)?;

    let z_1_shifted_lde = z_1_shifted.clone().coset_lde(&worker, 4)?;

    let z_2_lde = z_2.clone().coset_lde(&worker, 4)?;

    let z_2_shifted_lde = z_2_shifted.clone().coset_lde(&worker, 4)?;

    {
        // TODO: May be optimize number of additions
        let mut contrib_z_1 = z_1_lde.clone();

        let mut s_id_by_beta = s_id_lde;
        s_id_by_beta.scale(&worker, beta);

        let mut n_by_beta = n_fe;
        n_by_beta.mul_assign(&beta);

        let mut a_perm = s_id_by_beta.clone();
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_1.mul_assign(&worker, &a_perm);
        drop(a_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut b_perm = s_id_by_beta.clone();

        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_1.mul_assign(&worker, &b_perm);
        drop(b_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut c_perm = s_id_by_beta;
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_1.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_1.sub_assign(&worker, &z_1_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_1);
    }

        {
        // TODO: May be optimize number of additions
        let mut contrib_z_2 = z_2_lde.clone();

        let mut a_perm = sigma_1_lde;
        a_perm.scale(&worker, beta);
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_2.mul_assign(&worker, &a_perm);
        drop(a_perm);


        let mut b_perm = sigma_2_lde;
        b_perm.scale(&worker, beta);
        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_2.mul_assign(&worker, &b_perm);
        drop(b_perm);

        let mut c_perm = sigma_3_lde;
        c_perm.scale(&worker, beta);
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_2.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_2.sub_assign(&worker, &z_2_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_2);
    }

    drop(a_lde);
    drop(b_lde);
    drop(c_lde);

    let l_0 = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
    let l_n_minus_one = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

    {
        let mut z_1_minus_z_2_shifted = z_1_shifted_lde.clone();
        z_1_minus_z_2_shifted.sub_assign(&worker, &z_2_shifted_lde);

        let l = l_n_minus_one.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2_shifted.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2_shifted.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2_shifted);
    }

    {
        let mut z_1_minus_z_2= z_1_lde.clone();
        z_1_minus_z_2.sub_assign(&worker, &z_2_lde);

        let l = l_0.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2);
    }

    let t_poly = t_1.icoset_fft(&worker);

    println!("End work with polynomials");

    // let degree = get_degree::<E>(&t_poly);

    // assert!(degree <= 3*n);
    
    fn get_degree<E:Engine>(poly: &Polynomial<E::Fr, Coefficients>) -> usize {
        let mut degree = poly.as_ref().len() - 1;
        for c in poly.as_ref().iter().rev() {
            if c.is_zero() {
                degree -= 1;
            } else {
                break;
            }
        }

        println!("Degree = {}", degree);

        degree
    }

    let (t_commitment, t_aux) = large_committer.commit_single(&t_poly);

    transcript.commit_input(&t_commitment);

    let z = transcript.get_challenge();

    // this is a sanity check

    let a_at_z = a_poly.evaluate_at(&worker, z);
    let b_at_z = b_poly.evaluate_at(&worker, z);
    let c_at_z = c_poly.evaluate_at(&worker, z);

    let q_l_at_z = q_l.evaluate_at(&worker, z);
    let q_r_at_z = q_r.evaluate_at(&worker, z);
    let q_o_at_z = q_o.evaluate_at(&worker, z);
    let q_m_at_z = q_m.evaluate_at(&worker, z);
    let q_c_at_z = q_c.evaluate_at(&worker, z);

    let s_id_at_z = s_id.evaluate_at(&worker, z);
    let sigma_1_at_z = sigma_1.evaluate_at(&worker, z);
    let sigma_2_at_z = sigma_2.evaluate_at(&worker, z);
    let sigma_3_at_z = sigma_3.evaluate_at(&worker, z);

    let mut inverse_vanishing_at_z = assembly.evaluate_inverse_vanishing_poly(required_domain_size.next_power_of_two(), z);

    let z_1_at_z = z_1.evaluate_at(&worker, z);
    let z_2_at_z = z_2.evaluate_at(&worker, z);

    let z_1_shifted_at_z = z_1_shifted.evaluate_at(&worker, z);
    let z_2_shifted_at_z = z_2_shifted.evaluate_at(&worker, z);

    let t_at_z = t_poly.evaluate_at(&worker, z);

    let l_0_at_z = l_0.evaluate_at(&worker, z);
    let l_n_minus_one_at_z = l_n_minus_one.evaluate_at(&worker, z);

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

    // this is a sanity check
    {
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

        assert_eq!(t_at_z, t_1, "sanity check failed");
    }

    // we do NOT compute linearization polynomial for non-homomorphic case

    let mut z_by_omega = z;
    z_by_omega.mul_assign(&z_1.omega);

    let opening_polynomials = vec![
        &a_poly,
        &b_poly,
        &c_poly,
        &q_l,
        &q_r,
        &q_o,
        &q_m,
        &q_c,
        &s_id,
        &sigma_1,
        &sigma_2,
        &sigma_3,
        &z_1,
        &z_2,
        &z_1,
        &z_2,
    ];

    let degrees: Vec<usize> = opening_polynomials.iter().map(|el| el.size()).collect();

    let precomputations = Some(vec![
        a_aux_data.as_ref().expect("is some"),
        b_aux_data.as_ref().expect("is some"),
        c_aux_data.as_ref().expect("is some"),
        aux.q_l_aux.as_ref().expect("is some"),
        aux.q_r_aux.as_ref().expect("is some"),
        aux.q_o_aux.as_ref().expect("is some"),
        aux.q_m_aux.as_ref().expect("is some"),
        aux.q_c_aux.as_ref().expect("is some"),
        aux.s_id_aux.as_ref().expect("is some"),
        aux.sigma_1_aux.as_ref().expect("is some"),
        aux.sigma_2_aux.as_ref().expect("is some"),
        aux.sigma_3_aux.as_ref().expect("is some"),
        z_1_aux.as_ref().expect("is some"),
        z_2_aux.as_ref().expect("is some"),
        z_1_aux.as_ref().expect("is some"),
        z_2_aux.as_ref().expect("is some"),
    ]);

    let opening_values = vec![
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
        z_2_shifted_at_z
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

    let multiopen_proof = committer.open_multiple(
        opening_polynomials, 
        degrees, 
        aggregation_challenge,
        opening_points, 
        opening_values,
        &precomputations, 
        &mut transcript
    );

    let t_opening_proof = large_committer.open_single(
        &t_poly,
        z,
        t_at_z,
        &t_aux.as_ref(), 
        &mut transcript
    ); 



    // let opening_polynomials = vec![
    //     &z_1,
    //     &z_2,
    // ];

    // let degrees: Vec<usize> = opening_polynomials.iter().map(|el| el.size()).collect();

    // let precomputations = Some(vec![
    //     z_1_aux.as_ref().expect("is some"),
    //     z_2_aux.as_ref().expect("is some"),
    // ]);

    // let opening_values = vec![
    //     z_1_shifted_at_z,
    //     z_2_shifted_at_z
    // ];

    

    // let shifted_proof = committer.open_multiple(
    //     opening_polynomials, 
    //     degrees, 
    //     shifted_opening_aggregation_challenge,
    //     opening_point, 
    //     opening_values,
    //     &precomputations, 
    //     &mut transcript
    // );

    let proof = PlonkNonhomomorphicProof::<E, S> {
        a_opening_value: a_at_z,
        b_opening_value: b_at_z,
        c_opening_value: c_at_z,
        q_l_opening_value: q_l_at_z,
        q_r_opening_value: q_r_at_z,
        q_o_opening_value: q_o_at_z,
        q_m_opening_value: q_m_at_z,
        q_c_opening_value: q_c_at_z,
        s_id_opening_value: s_id_at_z,
        sigma_1_opening_value: sigma_1_at_z,
        sigma_2_opening_value: sigma_2_at_z,
        sigma_3_opening_value: sigma_3_at_z,
        z_1_unshifted_opening_value: z_1_at_z,
        z_2_unshifted_opening_value: z_2_at_z,
        z_1_shifted_opening_value: z_1_shifted_at_z,
        z_2_shifted_opening_value: z_2_shifted_at_z,
        t_opening_value: t_at_z,
        a_commitment: a_commitment,
        b_commitment: b_commitment,
        c_commitment: c_commitment,
        z_1_commitment: z_1_commitment,
        z_2_commitment: z_2_commitment,
        t_commitment: t_commitment,
        openings_proof: multiopen_proof,
        // shifted_openings_proof: shifted_proof,
        t_opening_proof: t_opening_proof,
    };

    Ok(proof)
}

pub fn prove_nonhomomorphic_chunked<E: Engine, S: CommitmentScheme<E::Fr, Prng = T>, T: Transcript<E::Fr, Input = S::Commitment>, C: Circuit<E>>(
    circuit: &C, 
    aux: &PlonkSetupAuxData<E, S>,
    meta: S::Meta,
) -> Result<PlonkChunkedNonhomomorphicProof<E, S>, SynthesisError> {
    assert!(S::IS_HOMOMORPHIC == false);

    let mut assembly = ProvingAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.num_gates();

    let committer = S::new_for_size(num_gates.next_power_of_two(), meta);

    let worker = Worker::new();

    let mut transcript = T::new();

    let n = assembly.input_gates.len() + assembly.aux_gates.len();

    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = n + 1;
    assert!(required_domain_size.is_power_of_two());

    println!("Start work with polynomials");

    let (w_l, w_r, w_o) = assembly.make_wire_assingments();

    let w_l = Polynomial::<E::Fr, Values>::from_values_unpadded(w_l)?;
    let w_r = Polynomial::<E::Fr, Values>::from_values_unpadded(w_r)?;
    let w_o = Polynomial::<E::Fr, Values>::from_values_unpadded(w_o)?;

    let a_poly = w_l.clone_padded_to_domain()?.ifft(&worker);
    let b_poly = w_r.clone_padded_to_domain()?.ifft(&worker);
    let c_poly = w_o.clone_padded_to_domain()?.ifft(&worker);

    let (a_commitment, a_aux_data) = committer.commit_single(&a_poly);
    let (b_commitment, b_aux_data) = committer.commit_single(&b_poly);
    let (c_commitment, c_aux_data) = committer.commit_single(&c_poly);

    transcript.commit_input(&a_commitment);
    transcript.commit_input(&b_commitment);
    transcript.commit_input(&c_commitment);

    // TODO: Add public inputs

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    let mut w_l_plus_gamma = w_l.clone();
    w_l_plus_gamma.add_constant(&worker, &gamma);

    let mut w_r_plus_gamma = w_r.clone();
    w_r_plus_gamma.add_constant(&worker, &gamma);

    let mut w_o_plus_gamma = w_o.clone();
    w_o_plus_gamma.add_constant(&worker, &gamma);

    let z_1 = {
        let n = assembly.input_gates.len() + assembly.aux_gates.len();
        let s_id_1: Vec<_> = (1..=n).collect();
        let s_id_1 = convert_to_field_elements(&s_id_1, &worker);
        let s_id_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &s_id_1, &beta);
        drop(s_id_1);

        let s_id_2: Vec<_> = ((n+1)..=(2*n)).collect();
        let s_id_2 = convert_to_field_elements(&s_id_2, &worker);
        let s_id_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &s_id_2, &beta);
        drop(s_id_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let s_id_3: Vec<_> = ((2*n+1)..=(3*n)).collect();
        let s_id_3 = convert_to_field_elements(&s_id_3, &worker);
        let s_id_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &s_id_3, &beta);
        drop(s_id_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        Polynomial::<E::Fr, Values>::from_values(prepadded)?
    };

    let z_2 = {
        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();

        let sigma_1 = convert_to_field_elements(&sigma_1, &worker);
        let sigma_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &sigma_1, &beta);
        drop(sigma_1);

        let sigma_2 = convert_to_field_elements(&sigma_2, &worker);
        let sigma_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &sigma_2, &beta);
        drop(sigma_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let sigma_3 = convert_to_field_elements(&sigma_3, &worker);
        let sigma_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &sigma_3, &beta);
        drop(sigma_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        let z_2 = Polynomial::<E::Fr, Values>::from_values(prepadded)?;

        z_2
    };

    let z_1 = z_1.ifft(&worker);
    let z_2 = z_2.ifft(&worker);

    let (z_1_commitment, z_1_aux) = committer.commit_single(&z_1);
    let (z_2_commitment, z_2_aux) = committer.commit_single(&z_2);

    transcript.commit_input(&z_1_commitment);
    transcript.commit_input(&z_2_commitment);

    let mut z_1_shifted = z_1.clone();
    z_1_shifted.distribute_powers(&worker, z_1.omega);
    
    let mut z_2_shifted = z_2.clone();
    z_2_shifted.distribute_powers(&worker, z_2.omega);
    
    let a_lde = a_poly.clone().coset_lde(&worker, 4)?;
    let b_lde = b_poly.clone().coset_lde(&worker, 4)?;
    let c_lde = c_poly.clone().coset_lde(&worker, 4)?;

    let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = assembly.output_setup_polynomials(&worker)?;

    let q_l_lde = q_l.clone().coset_lde(&worker, 4)?;
    let q_r_lde = q_r.clone().coset_lde(&worker, 4)?;
    let q_o_lde = q_o.clone().coset_lde(&worker, 4)?;
    let q_m_lde = q_m.clone().coset_lde(&worker, 4)?;
    let q_c_lde = q_c.clone().coset_lde(&worker, 4)?;
    let s_id_lde = s_id.clone().coset_lde(&worker, 4)?;
    let sigma_1_lde = sigma_1.clone().coset_lde(&worker, 4)?;
    let sigma_2_lde = sigma_2.clone().coset_lde(&worker, 4)?;
    let sigma_3_lde = sigma_3.clone().coset_lde(&worker, 4)?;

    // we do not commit those cause those are known already

    let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    let alpha = transcript.get_challenge();

    let mut vanishing_poly_inverse = assembly.calculate_inverse_vanishing_polynomial_in_a_coset(&worker, q_c_lde.size(), required_domain_size.next_power_of_two())?;

    let mut t_1 = {
        let mut t_1 = q_c_lde;

        let mut q_l_by_a = q_l_lde;
        q_l_by_a.mul_assign(&worker, &a_lde);
        t_1.add_assign(&worker, &q_l_by_a);
        drop(q_l_by_a);

        let mut q_r_by_b = q_r_lde;
        q_r_by_b.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_r_by_b);
        drop(q_r_by_b);

        let mut q_o_by_c = q_o_lde;
        q_o_by_c.mul_assign(&worker, &c_lde);
        t_1.add_assign(&worker, &q_o_by_c);
        drop(q_o_by_c);

        let mut q_m_by_ab = q_m_lde;
        q_m_by_ab.mul_assign(&worker, &a_lde);
        q_m_by_ab.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_m_by_ab);
        drop(q_m_by_ab);

        vanishing_poly_inverse.scale(&worker, alpha);

        t_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1
    };

    let z_1_lde = z_1.clone().coset_lde(&worker, 4)?;

    let z_1_shifted_lde = z_1_shifted.clone().coset_lde(&worker, 4)?;

    let z_2_lde = z_2.clone().coset_lde(&worker, 4)?;

    let z_2_shifted_lde = z_2_shifted.clone().coset_lde(&worker, 4)?;

    {
        // TODO: May be optimize number of additions
        let mut contrib_z_1 = z_1_lde.clone();

        let mut s_id_by_beta = s_id_lde;
        s_id_by_beta.scale(&worker, beta);

        let mut n_by_beta = n_fe;
        n_by_beta.mul_assign(&beta);

        let mut a_perm = s_id_by_beta.clone();
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_1.mul_assign(&worker, &a_perm);
        drop(a_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut b_perm = s_id_by_beta.clone();

        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_1.mul_assign(&worker, &b_perm);
        drop(b_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut c_perm = s_id_by_beta;
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_1.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_1.sub_assign(&worker, &z_1_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_1);
    }

        {
        // TODO: May be optimize number of additions
        let mut contrib_z_2 = z_2_lde.clone();

        let mut a_perm = sigma_1_lde;
        a_perm.scale(&worker, beta);
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_2.mul_assign(&worker, &a_perm);
        drop(a_perm);


        let mut b_perm = sigma_2_lde;
        b_perm.scale(&worker, beta);
        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_2.mul_assign(&worker, &b_perm);
        drop(b_perm);

        let mut c_perm = sigma_3_lde;
        c_perm.scale(&worker, beta);
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_2.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_2.sub_assign(&worker, &z_2_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_2);
    }

    drop(a_lde);
    drop(b_lde);
    drop(c_lde);

    let l_0 = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
    let l_n_minus_one = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

    {
        let mut z_1_minus_z_2_shifted = z_1_shifted_lde.clone();
        z_1_minus_z_2_shifted.sub_assign(&worker, &z_2_shifted_lde);

        let l = l_n_minus_one.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2_shifted.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2_shifted.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2_shifted);
    }

    {
        let mut z_1_minus_z_2= z_1_lde.clone();
        z_1_minus_z_2.sub_assign(&worker, &z_2_lde);

        let l = l_0.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2);
    }

    let t_poly = t_1.icoset_fft(&worker);

    println!("End work with polynomials");

    let mut t_poly_parts = t_poly.break_into_multiples(required_domain_size)?;

    t_poly_parts.pop().expect("last part is irrelevant");
    let t_poly_high = t_poly_parts.pop().expect("high exists");
    let t_poly_mid = t_poly_parts.pop().expect("mid exists");
    let t_poly_low = t_poly_parts.pop().expect("low exists");

    let (t_low_commitment, t_low_aux) = committer.commit_single(&t_poly_low);
    let (t_mid_commitment, t_mid_aux) = committer.commit_single(&t_poly_mid);
    let (t_high_commitment, t_high_aux) = committer.commit_single(&t_poly_high);

    transcript.commit_input(&t_low_commitment);
    transcript.commit_input(&t_mid_commitment);
    transcript.commit_input(&t_high_commitment);

    let z = transcript.get_challenge();

    let a_at_z = a_poly.evaluate_at(&worker, z);
    let b_at_z = b_poly.evaluate_at(&worker, z);
    let c_at_z = c_poly.evaluate_at(&worker, z);

    let q_l_at_z = q_l.evaluate_at(&worker, z);
    let q_r_at_z = q_r.evaluate_at(&worker, z);
    let q_o_at_z = q_o.evaluate_at(&worker, z);
    let q_m_at_z = q_m.evaluate_at(&worker, z);
    let q_c_at_z = q_c.evaluate_at(&worker, z);

    let s_id_at_z = s_id.evaluate_at(&worker, z);
    let sigma_1_at_z = sigma_1.evaluate_at(&worker, z);
    let sigma_2_at_z = sigma_2.evaluate_at(&worker, z);
    let sigma_3_at_z = sigma_3.evaluate_at(&worker, z);

    let mut inverse_vanishing_at_z = assembly.evaluate_inverse_vanishing_poly(required_domain_size.next_power_of_two(), z);

    let z_1_at_z = z_1.evaluate_at(&worker, z);
    let z_2_at_z = z_2.evaluate_at(&worker, z);

    let z_1_shifted_at_z = z_1_shifted.evaluate_at(&worker, z);
    let z_2_shifted_at_z = z_2_shifted.evaluate_at(&worker, z);

    let t_low_at_z = t_poly_low.evaluate_at(&worker, z);
    let t_mid_at_z = t_poly_mid.evaluate_at(&worker, z);
    let t_high_at_z = t_poly_high.evaluate_at(&worker, z);

    let l_0_at_z = l_0.evaluate_at(&worker, z);
    let l_n_minus_one_at_z = l_n_minus_one.evaluate_at(&worker, z);

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

    let z_in_pow_of_domain_size = z.pow([required_domain_size as u64]);

    // this is a sanity check
    {
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

        let mut t_at_z = E::Fr::zero();
        t_at_z.add_assign(&t_low_at_z);

        let mut tmp = z_in_pow_of_domain_size;
        tmp.mul_assign(&t_mid_at_z);
        t_at_z.add_assign(&tmp);

        let mut tmp = z_in_pow_of_domain_size;
        tmp.mul_assign(&z_in_pow_of_domain_size);
        tmp.mul_assign(&t_high_at_z);
        t_at_z.add_assign(&tmp);

        assert_eq!(t_at_z, t_1, "sanity check failed");
    }

    // we do NOT compute linearization polynomial for non-homomorphic case

    let mut z_by_omega = z;
    z_by_omega.mul_assign(&z_1.omega);

    let opening_polynomials = vec![
        &a_poly,
        &b_poly,
        &c_poly,
        &q_l,
        &q_r,
        &q_o,
        &q_m,
        &q_c,
        &s_id,
        &sigma_1,
        &sigma_2,
        &sigma_3,
        &z_1,
        &z_2,
        &z_1,
        &z_2,
        &t_poly_low,
        &t_poly_mid,
        &t_poly_high
    ];

    let degrees: Vec<usize> = opening_polynomials.iter().map(|el| el.size()).collect();

    let precomputations = Some(vec![
        a_aux_data.as_ref().expect("is some"),
        b_aux_data.as_ref().expect("is some"),
        c_aux_data.as_ref().expect("is some"),
        aux.q_l_aux.as_ref().expect("is some"),
        aux.q_r_aux.as_ref().expect("is some"),
        aux.q_o_aux.as_ref().expect("is some"),
        aux.q_m_aux.as_ref().expect("is some"),
        aux.q_c_aux.as_ref().expect("is some"),
        aux.s_id_aux.as_ref().expect("is some"),
        aux.sigma_1_aux.as_ref().expect("is some"),
        aux.sigma_2_aux.as_ref().expect("is some"),
        aux.sigma_3_aux.as_ref().expect("is some"),
        z_1_aux.as_ref().expect("is some"),
        z_2_aux.as_ref().expect("is some"),
        z_1_aux.as_ref().expect("is some"),
        z_2_aux.as_ref().expect("is some"),
        t_low_aux.as_ref().expect("is some"),
        t_mid_aux.as_ref().expect("is some"),
        t_high_aux.as_ref().expect("is some"),
    ]);

    let opening_values = vec![
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

    let multiopen_proof = committer.open_multiple(
        opening_polynomials, 
        degrees, 
        aggregation_challenge,
        opening_points, 
        opening_values,
        &precomputations, 
        &mut transcript
    );

    let proof = PlonkChunkedNonhomomorphicProof::<E, S> {
        a_opening_value: a_at_z,
        b_opening_value: b_at_z,
        c_opening_value: c_at_z,
        q_l_opening_value: q_l_at_z,
        q_r_opening_value: q_r_at_z,
        q_o_opening_value: q_o_at_z,
        q_m_opening_value: q_m_at_z,
        q_c_opening_value: q_c_at_z,
        s_id_opening_value: s_id_at_z,
        sigma_1_opening_value: sigma_1_at_z,
        sigma_2_opening_value: sigma_2_at_z,
        sigma_3_opening_value: sigma_3_at_z,
        z_1_unshifted_opening_value: z_1_at_z,
        z_2_unshifted_opening_value: z_2_at_z,
        z_1_shifted_opening_value: z_1_shifted_at_z,
        z_2_shifted_opening_value: z_2_shifted_at_z,
        t_low_opening_value: t_low_at_z,
        t_mid_opening_value: t_mid_at_z,
        t_high_opening_value: t_high_at_z,
        a_commitment: a_commitment,
        b_commitment: b_commitment,
        c_commitment: c_commitment,
        z_1_commitment: z_1_commitment,
        z_2_commitment: z_2_commitment,
        t_low_commitment: t_low_commitment,
        t_mid_commitment: t_mid_commitment,
        t_high_commitment: t_high_commitment,
        openings_proof: multiopen_proof,
    };

    Ok(proof)
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

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

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
    fn test_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};

        let mut assembly = ProvingAssembly::<Bn256>::new();

        let circuit = TestCircuit::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        println!("{:?}", assembly);

        assembly.finalize();

        let (f_l, f_r, f_o) = assembly.make_wire_assingments();

        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();

        let num_gates = assembly.num_gates();

        let id_1: Vec<_> = (1..=num_gates).collect();
        let id_2: Vec<_> = ((num_gates+1)..=(2*num_gates)).collect();
        let id_3: Vec<_> = ((2*num_gates + 1)..=(3*num_gates)).collect();

        let beta = Fr::from_str("15").unwrap();
        let gamma = Fr::from_str("4").unwrap();

        let mut f_1_poly = vec![];
        let mut g_1_poly = vec![];
        for (i, el) in f_l.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_1[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_1_poly.push(tmp);
        }

        for (i, el) in f_l.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_1[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_1_poly.push(tmp);
        }

        let mut f_2_poly = vec![];
        let mut g_2_poly = vec![];
        for (i, el) in f_r.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_2[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_2_poly.push(tmp);
        }

        for (i, el) in f_r.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_2[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_2_poly.push(tmp);
        }


        let mut f_3_poly = vec![];
        let mut g_3_poly = vec![];
        for (i, el) in f_o.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_3[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_3_poly.push(tmp);
        }

        for (i, el) in f_o.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_3[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_3_poly.push(tmp);
        }

        let mut f_poly = vec![];
        let mut g_poly = vec![];

        for i in 0..f_1_poly.len() {
            let mut tmp = f_1_poly[i];
            tmp.mul_assign(&f_2_poly[i]);
            tmp.mul_assign(&f_3_poly[i]);
            f_poly.push(tmp);
        }

        for i in 0..g_1_poly.len() {
            let mut tmp = g_1_poly[i];
            tmp.mul_assign(&g_2_poly[i]);
            tmp.mul_assign(&g_3_poly[i]);
            g_poly.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut f_prime = vec![tmp];
        for el in f_poly.iter() {
            tmp.mul_assign(&el);
            f_prime.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut g_prime = vec![tmp];
        for el in g_poly.iter() {
            tmp.mul_assign(&el);
            g_prime.push(tmp);
        }

        assert!(f_prime[0] == g_prime[0]);
        assert!(f_prime[num_gates] == g_prime[num_gates]);

        let worker = Worker::new();

        let _ = assembly.output_setup_polynomials(&worker).unwrap();
    }
}