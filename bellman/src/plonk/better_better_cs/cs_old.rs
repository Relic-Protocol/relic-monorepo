use crate::pairing::ff::{Field};
use crate::pairing::{Engine};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::worker::Worker;
use crate::plonk::domains::*;
use crate::plonk::polynomials::*;

pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;

pub trait Circuit<E: Engine> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolynomialInConstraint {
    VariablesPolynomial(usize, TimeDilation),
    WitnessPolynomial(usize, TimeDilation),
    SetupPolynomial(&'static str, usize, TimeDilation)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Coefficient {
    PlusOne,
    MinusOne,
    Other
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolyIdentifier {
    VariablesPolynomial(usize),
    WitnessPolynomial(usize),
    SetupPolynomial(&'static str, usize),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TimeDilation(pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialMultiplicativeTerm(pub Coefficient, pub Vec<PolynomialInConstraint>);

impl PolynomialMultiplicativeTerm {
    fn degree(&self) -> usize {
        self.1.len()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct LinearCombinationOfTerms(pub Vec<PolynomialMultiplicativeTerm>);

impl LinearCombinationOfTerms {
    fn terms(&self) -> &[PolynomialMultiplicativeTerm] {
       &self.0[..]
    }
}

pub enum ArithmeticTerm<E: Engine>{
    Product(Vec<Variable>, E::Fr),
    SingleVariable(Variable, E::Fr),
    Constant(E::Fr),
}

impl<E: Engine> ArithmeticTerm<E> {
    pub fn from_variable(var: Variable) -> Self {
        ArithmeticTerm::SingleVariable(var, E::Fr::one())
    }

    pub fn from_variable_and_coeff(var: Variable, coeff: E::Fr) -> Self {
        ArithmeticTerm::SingleVariable(var, coeff)
    }

    pub fn constant(coeff: E::Fr) -> Self {
        ArithmeticTerm::Constant(coeff)
    }

    pub fn mul_by_variable(self, other: Variable) -> Self {
        match self {
            ArithmeticTerm::Product(mut terms, coeff) => {
                terms.push(other);

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::SingleVariable(this, coeff) => {
                let terms = vec![this, other];

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::Constant(coeff) => {
                let terms = vec![other];

                ArithmeticTerm::Product(terms, coeff)
            },
        }
    }

    pub fn scale(&mut self, by: &E::Fr) {
        match self {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.mul_assign(by);
            },
        }
    }
}

pub struct MainGateTerm<E: Engine>{
    terms: Vec<ArithmeticTerm<E>>,
    num_multiplicative_terms: usize,
    num_constant_terms: usize
}

impl<E: Engine> MainGateTerm<E> {
    pub fn new() -> Self {
        Self {
            terms: Vec::with_capacity(8),
            num_multiplicative_terms: 0,
            num_constant_terms: 0
        }
    }

    pub fn len_without_constant(&self) -> usize {
        self.terms.len()
    }

    pub fn add_assign(&mut self, other: ArithmeticTerm<E>) {
        match &other {
            ArithmeticTerm::Product(_, _) => {
                self.num_multiplicative_terms += 1;
                self.terms.push(other);
            },
            ArithmeticTerm::SingleVariable(_, _) => {
                self.terms.push(other);
            },
            ArithmeticTerm::Constant(_) => {
                self.num_constant_terms += 1;
                self.terms.push(other);
            },
        }

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }

    pub fn sub_assign(&mut self, mut other: ArithmeticTerm<E>) {
        match &mut other {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.negate();
                self.num_multiplicative_terms += 1;
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.negate();
                self.num_constant_terms += 1;       
            },
        }

        self.terms.push(other);

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }
}

pub trait MainGateEquation: GateEquation {
    const NUM_LINEAR_TERMS: usize;
    const NUM_VARIABLES: usize;
    const NUM_VARIABLES_ON_NEXT_STEP: usize;
    fn range_of_multiplicative_term() -> std::ops::Range<usize>;
    fn range_of_linear_terms() -> std::ops::Range<usize>;
    fn index_for_constant_term() -> usize;
    fn range_of_next_step_linear_terms() -> std::ops::Range<usize>;
    fn format_term<E: Engine>(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
}

pub trait GateEquation: GateEquationInternal
    + Sized
    + Clone
    + std::hash::Hash
    + std::default::Default 
{
    const HAS_NONTRIVIAL_CONSTANTS: bool;
    const NUM_CONSTANTS: usize;

    fn as_internal(&self) -> &dyn GateEquationInternal {
        self as &dyn GateEquationInternal
    }

    fn into_internal(self) -> Box<dyn GateEquationInternal> {
        Box::from(self) as Box<dyn GateEquationInternal>
    }

    fn static_description() -> &'static Self;

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr>;
}

pub trait GateEquationInternal: Send 
    + Sync 
    + 'static 
    + std::any::Any 
    + std::fmt::Debug
{
    fn degree(&self) -> usize;
    fn num_constraints(&self) -> usize;
    fn can_include_public_inputs(&self) -> bool;
    fn put_public_inputs_into_selector_id(&self) -> Option<usize>;
    fn get_constraint(&self) -> &LinearCombinationOfTerms;
    fn get_constraints(&self) -> &[LinearCombinationOfTerms];
}

impl std::hash::Hash for dyn GateEquationInternal {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        self.type_id().hash(state);
        self.degree().hash(state);
        for t in self.get_constraints().iter() {
            t.hash(state);
        }
    }
}

impl PartialEq for dyn GateEquationInternal {
    fn eq(&self, other: &Self) -> bool {
        self.degree() == other.degree() &&
        self.get_constraints() == other.get_constraints()
    }
}

impl Eq for dyn GateEquationInternal {}

#[derive(Clone, Debug, Hash)]
pub struct Width4MainGateWithDNextEquation(pub [LinearCombinationOfTerms; 1]);

impl GateEquationInternal for Width4MainGateWithDNextEquation {
    fn degree(&self) -> usize {
        3
    }

    fn num_constraints(&self) -> usize {
        1
    }

    fn can_include_public_inputs(&self) -> bool {
        true
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        Some(5)
    }

    fn get_constraint(&self) -> &LinearCombinationOfTerms {
        &(self.0[0])
    }

    fn get_constraints(&self) -> &[LinearCombinationOfTerms] {
        &self.0[..]
    }
}

impl GateEquation for Width4MainGateWithDNextEquation {
    const HAS_NONTRIVIAL_CONSTANTS: bool = false;
    const NUM_CONSTANTS: usize = 7;

    // Width4MainGateWithDNextEquation is NOT generic, so this is fine
    // and safe since it's sync!
    fn static_description() -> &'static Self {
        static mut VALUE: Option<Width4MainGateWithDNextEquation> = None;
        static INIT: std::sync::Once = std::sync::Once::new();

        unsafe {
            INIT.call_once(||{
                VALUE = Some(Width4MainGateWithDNextEquation::default());
            });

            VALUE.as_ref().unwrap()
        }
    }

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr> {
        vec![E::Fr::one(); 7]
    }
}


struct SimpleBitmap(u64, usize);
impl SimpleBitmap {
    fn new() -> Self {
        Self(0u64, 0)
    }

    fn get_next_unused(&mut self) -> usize {
        for i in 0..64 {
            if self.get(i) == false {
                return i;
            }
        }

        unreachable!()
    }

    fn get(&self, idx: usize) -> bool{
        1u64 << idx & self.0 > 0
    }

    fn set(&mut self, idx: usize) {
        self.0 |= 1u64 << idx;
    }
}

impl MainGateEquation for Width4MainGateWithDNextEquation {
    const NUM_LINEAR_TERMS: usize = 4;
    const NUM_VARIABLES: usize = 4;
    const NUM_VARIABLES_ON_NEXT_STEP: usize = 1;

    fn range_of_multiplicative_term() -> std::ops::Range<usize> {
        0..2
    }
    fn range_of_linear_terms() -> std::ops::Range<usize> {
        0..4
    }

    fn index_for_constant_term() -> usize {
        5
    }

    fn range_of_next_step_linear_terms() -> std::ops::Range<usize> {
        6..7
    }

    fn format_term<E: Engine>(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        let mut flattened_variables = vec![padding; Self::NUM_VARIABLES];
        let mut flattened_coefficients = vec![E::Fr::zero(); 7];
        let mut bitmap = SimpleBitmap::new();

        let allowed_linear = 4;
        let allowed_multiplications = 1;
        let allowed_constants = 1;

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
                    flattened_coefficients[4] = coeff;
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
                    flattened_coefficients[5] = coeff;
                },
                _ => {
                    unreachable!("must be multiplicative term");
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
                        // there is some variable there already,
                        flattened_coefficients[index] = coeff;
                    } else {
                        let idx = bitmap.get_next_unused();
                        flattened_variables[idx] = var;
                        flattened_coefficients[idx] = coeff;
                        bitmap.set(idx);
                    }
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }
}

impl std::default::Default for Width4MainGateWithDNextEquation {
    fn default() -> Self {
        Self::get_equation()
    }
}

impl Width4MainGateWithDNextEquation {
    pub fn get_equation() -> Self {
        let mut terms: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(7);
        // linear terms
        for i in 0..4 {
            // N * Q_n
            terms.push(
                PolynomialMultiplicativeTerm(
                    Coefficient::PlusOne,
                    vec![
                        PolynomialInConstraint::VariablesPolynomial(i, TimeDilation(0)), 
                        PolynomialInConstraint::SetupPolynomial("main gate of width 4", i, TimeDilation(0))
                    ]
                )
            );
        }

        // multiplication
        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)), 
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)), 
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 4, TimeDilation(0))
                ]
            )
        );

        // constant
        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 5, TimeDilation(0))
                ]
            )
        );

        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)), 
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 6, TimeDilation(0))
                ]
            )
        );

        Self([LinearCombinationOfTerms(terms)])
    }
}

fn check_gate_to_support_public_inputs<G: GateEquation>(gate: &G) -> bool {
    for t in gate.get_constraints() {
        for c in t.0.iter() {
            if c.1.len() != 1 {
                continue;
            }
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::SetupPolynomial(..) => {
                        return true;
                    },
                    _ => {}
                }
            }
        }
    }

    false
}

fn has_access_to_next_step<G: GateEquation>(gate: &G) -> bool {
    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                    PolynomialInConstraint::WitnessPolynomial(_, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                    PolynomialInConstraint::SetupPolynomial(_, _, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                }
            }
        }
    }

    false
}

fn max_addressed_state_poly<G: GateEquation>(gate: &G) -> Option<usize> {
    let mut max: Option<usize> = None;

    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::VariablesPolynomial(idx, _) => {
                        let new_max = match max.take() {
                            Some(value) => {
                                if value < *idx {
                                    Some(*idx)
                                } else {
                                    Some(value)
                                }
                            },
                            None => {
                                Some(*idx)
                            }
                        };

                        max = new_max;
                    },
                    _ => {}
                }
            }
        }
    }

    max
}

fn max_addressed_witness_poly<G: GateEquation>(gate: &G) -> Option<usize> {
    let mut max: Option<usize> = None;

    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::WitnessPolynomial(idx, _) => {
                        let new_max = match max.take() {
                            Some(value) => {
                                if value < *idx {
                                    Some(*idx)
                                } else {
                                    Some(value)
                                }
                            },
                            None => {
                                Some(*idx)
                            }
                        };

                        max = new_max;
                    },
                    _ => {}
                }
            }
        }
    }

    max
}

// fn max_addressed_setup_poly<G: GateEquation>(gate: &G) -> Option<(usize, &'static str)> {
//     let mut max: Option<usize> = None;

//     let mut setup_tag = None;

//     for t in gate.get_constraints() {
//         for c in t.0.iter() {
//             for s in c.0.iter() {
//                 match s {
//                     PolynomialInConstraint::SetupPolynomial(name, idx, _) => {
//                         let new_max = match max.take() {
//                             Some(value) => {
//                                 if value < *idx {
//                                     Some(*idx)
//                                 } else {
//                                     Some(value)
//                                 }
//                             },
//                             None => {
//                                 Some(*idx)
//                             }
//                         };

//                         max = new_max;
//                     },
//                     _ => {}
//                 }
//             }
//         }
//     }

//     max
// }

fn check_gate_is_allowed_for_params<E: Engine, P: PlonkConstraintSystemParams<E>, G: GateEquation>(
    gate: &G
) -> bool {
    let mut max_state = max_addressed_state_poly(gate);
    let mut max_witness = max_addressed_witness_poly(gate);
    // let max_setup = max_addressed_setup_poly(gate);

    let accesses_other_rows = has_access_to_next_step(gate);
    if accesses_other_rows && P::CAN_ACCESS_NEXT_TRACE_STEP == false {
        return false;
    }

    match max_state.take() {
        Some(m) => {
            if m > P::STATE_WIDTH {
                return false;
            }
        },
        _ => {}
    }

    match max_witness.take() {
        Some(m) => {
            if m > P::WITNESS_WIDTH {
                return false;
            }
        },
        _ => {}
    }

    true
}

pub trait PlonkConstraintSystemParams<E: Engine>: Sized + Copy + Clone + Send + Sync {
    const STATE_WIDTH: usize;
    const WITNESS_WIDTH: usize;
    const HAS_WITNESS_POLYNOMIALS: bool;
    const HAS_CUSTOM_GATES: bool;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool;
}

pub trait ConstraintSystem<E: Engine> {
    type Params: PlonkConstraintSystemParams<E>;
    type MainGate: MainGateEquation;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn new_single_gate_for_trace_step<G: GateEquation>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        self.begin_gates_batch_for_step()?;
        self.new_gate_in_batch(
            equation,
            coefficients_assignments,
            variables_assignments,
            witness_assignments
        )?;
        self.end_gates_batch_for_step()
    }

    fn get_main_gate(&self) -> &Self::MainGate;

    fn allocate_main_gate(&mut self, gate: MainGateTerm<E>) -> Result<(), SynthesisError> {
        let (vars, coeffs) = Self::MainGate::format_term(gate, Self::get_dummy_variable())?;

        let mg = Self::MainGate::static_description();

        self.new_single_gate_for_trace_step(
            mg,
            &coeffs,
            &vars,
            &[]
        )
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;
    fn new_gate_in_batch<G: GateEquation>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;
    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable() -> Variable;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PlonkCsWidth4WithNextStepParams;
impl<E: Engine> PlonkConstraintSystemParams<E> for PlonkCsWidth4WithNextStepParams {
    const STATE_WIDTH: usize =  4;
    const WITNESS_WIDTH: usize = 0;
    const HAS_WITNESS_POLYNOMIALS: bool = false;
    const HAS_CUSTOM_GATES: bool =  false;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool = true;
}

use crate::plonk::polynomials::*;

// pub struct PolynomialStorage<E: Engine> {
//     pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
//     pub witness_map: std::collections::HashMap<PolyIdentifier,Polynomial<E::Fr, Values>>,
//     pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
// }

pub struct PolynomialStorage<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Vec<Variable>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
}

impl<E: Engine> PolynomialStorage<E> {
    pub fn new() -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
        }
    }

    pub fn get_value(&self, poly: &PolynomialInConstraint, n: usize) -> Result<E::Fr, SynthesisError> {
        match poly {
            PolynomialInConstraint::VariablesPolynomial(_, _) => {
                unreachable!("should not try to get value of the state polynomial, get variable first instead");
            },
            PolynomialInConstraint::SetupPolynomial(gate_descr, idx, TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::SetupPolynomial(gate_descr, *idx);
                let value = *self.setup_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            PolynomialInConstraint::WitnessPolynomial(_, _) => {
                unimplemented!()
            }
        }
    }

    pub fn get_variable(&self, poly: &PolynomialInConstraint, n: usize) -> Result<Variable, SynthesisError> {
        match poly {
            PolynomialInConstraint::VariablesPolynomial(idx, TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::VariablesPolynomial(*idx);
                let value = *self.state_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            _ => {
                unreachable!("should not try to get variable of setup or witness polynomial");
            }
        }
    }

    // pub fn sort_by_public_inputs(&mut self, inputs_map: &[usize]) {
    //     for (_, storage) in self.state_map.iter_mut() {
    //         for (input_idx, gate_idx) in inputs_map.iter().enumerate() {
    //             storage.swap(*gate_idx, input_idx);
    //         }
    //     }
    //     for (_, storage) in self.setup_map.iter_mut() {
    //         for (input_idx, gate_idx) in inputs_map.iter().enumerate() {
    //             storage.swap(*gate_idx, input_idx);
    //         }
    //     }
    //     for (_, storage) in self.witness_map.iter_mut() {
    //         for (input_idx, gate_idx) in inputs_map.iter().enumerate() {
    //             storage.swap(*gate_idx, input_idx);
    //         }
    //     }
    // }
}

pub struct GateDensityStorage(pub std::collections::HashMap<Box<dyn GateEquationInternal>, BitVec>);

impl GateDensityStorage {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }

    // pub fn sort_by_public_inputs(&mut self, inputs_map: &[usize]) {
    //     if self.0.is_empty() {
    //         return;
    //     }

    //     for (_, density) in self.0.iter_mut() {
    //         for (input_idx, gate_idx) in inputs_map.iter().enumerate() {
    //             let value_at_n = density[*gate_idx];
    //             assert!(value_at_n, "main gate must be set at public input");
    //             let value_at_input_index = density[input_idx];

    //             density.set(*gate_idx, value_at_input_index);
    //             density.set(input_idx, value_at_n);
    //         }
    //     }
    // }
}

pub struct GateConstantCoefficientsStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateEquationInternal>, Vec<E::Fr>>);

impl<E: Engine> GateConstantCoefficientsStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub struct TrivialAssembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> {
    pub inputs_storage: PolynomialStorage<E>,
    pub aux_storage: PolynomialStorage<E>,
    pub num_input_gates: usize,
    pub num_aux_gates: usize,
    pub max_constraint_degree: usize,
    pub main_gate: MG,
    pub input_assingments: Vec<E::Fr>,
    pub aux_assingments: Vec<E::Fr>,
    pub num_inputs: usize,
    pub num_aux: usize,
    pub trace_step_for_batch: Option<usize>,
    pub is_finalized: bool,
    pub constraints: std::collections::HashSet<Box<dyn GateEquationInternal>>,
    pub gate_internal_coefficients: GateConstantCoefficientsStorage<E>,
    pub sorted_setup_polynomial_ids: Vec<PolyIdentifier>,
    pub sorted_gates: Vec<Box<dyn GateEquationInternal>>,
    pub sorted_gate_constants: Vec<Vec<E::Fr>>,
    pub aux_gate_density: GateDensityStorage,
    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> ConstraintSystem<E> for TrivialAssembly<E, P, MG> {
    type Params = P;
    type MainGate = MG;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        // println!("Allocated variable Aux({}) with value {}", index, value);

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

        let mut main_gate = MainGateTerm::<E>::new();
        main_gate.sub_assign(ArithmeticTerm::from_variable(input_var));

        let dummy = Self::get_dummy_variable();
        let (variables_assignments, coefficients_assignments) = MG::format_term(main_gate, dummy).expect("must make empty padding gate");

        let n = self.num_input_gates;
        Self::allocate_into_storage(
            MG::static_description(), 
            &mut self.inputs_storage, 
            n, 
            &coefficients_assignments, 
            &variables_assignments, 
            &[]
        )?;

        self.num_input_gates += 1;

        Ok(input_var)
    }

    fn get_main_gate(&self) -> &MG {
        &self.main_gate
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_none());
        self.num_aux_gates += 1;
        let n = self.num_aux_gates;
        self.trace_step_for_batch = Some(n);

        Ok(())
    }

    fn new_gate_in_batch<G: GateEquation>(&mut self, 
        gate: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        // check that gate is ok for config
        debug_assert!(check_gate_is_allowed_for_params::<E, P, G>(&gate), "supplied params do not work with gate {:?}", gate);

        let n = self.trace_step_for_batch.unwrap();
        // make zero-enumerated index
        let n = n - 1;
        
        Self::allocate_into_storage(
            gate,
            &mut self.aux_storage,
            n,
            coefficients_assignments,
            variables_assignments,
            witness_assignments
        )?;

        self.add_gate_into_list(gate);

        if let Some(tracker) = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateEquationInternal) {
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());
        } else {
            self.aux_gate_density.0.insert(gate.clone().into_internal(), BitVec::new());
            let tracker = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateEquationInternal).unwrap();
            tracker.grow(n, false);
            tracker.push(true);
        }

        Ok(())
    }

    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_some());
        let n = self.trace_step_for_batch.take().unwrap();
        debug_assert_eq!(n, self.num_aux_gates, "invalid batch id");

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                return Err(SynthesisError::AssignmentMissing);
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

    fn get_dummy_variable() -> Variable {
        Self::dummy_variable()
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> TrivialAssembly<E, P, MG> {
    fn allocate_into_storage<G: GateEquation>(
        gate: &G,
        storage: &mut PolynomialStorage<E>, 
        n: usize,coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        let dummy = Self::get_dummy_variable();
        let zero = E::Fr::zero();

        let mut coeffs_it = coefficients_assignments.iter();

        let mut setup_index: Option<(&'static str, usize)> = None;
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::SetupPolynomial(name, idx, _) => {
                            setup_index = Some((name, *idx));
                        },
                        _ => {}
                    }

                    match setup_index.take() {
                        Some((name, idx)) => {
                            let key = PolyIdentifier::SetupPolynomial(name, idx);
                            let poly_ref = storage.setup_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, E::Fr::zero());
                            }
                            poly_ref.push(*coeffs_it.next().unwrap_or(&zero));
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        let mut variable_index: Option<usize> = None;

        let mut variable_it = variables_assignments.iter();

        // go through all used variables to place them into the STATE
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::VariablesPolynomial(idx, TimeDilation(0)) => {
                            variable_index = Some(*idx);
                        }
                        PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(_)) => {
                            // gate can only have power over the current step
                        },
                        _ => {}
                    }

                    match variable_index.take() {
                        Some(idx) => {
                            let key = PolyIdentifier::VariablesPolynomial(idx);
                            let poly_ref = storage.state_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, dummy);
                            } else if poly_ref.len() == n {
                                // we consume variable only ONCE
                                let var = *variable_it.next().unwrap_or(&dummy);
                                poly_ref.push(var);
                            }
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(variable_it.next().is_none(), "must consume all variables for gate");

        let mut witness_it = witness_assignments.iter();

        let mut witness_index: Option<usize> = None;

        // go through all used variables to place them into the STATE
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::WitnessPolynomial(idx, TimeDilation(0)) => {
                            witness_index = Some(*idx);
                        },
                        _ => {}
                    }

                    match witness_index.take() {
                        Some(idx) => {
                            let key = PolyIdentifier::VariablesPolynomial(idx);
                            let poly_ref = storage.witness_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, E::Fr::zero());
                            } 
                            poly_ref.push(*witness_it.next().unwrap_or(&zero));
                        },
                        _ => {}
                    }
                }
            }
        }

        Ok(())
    }

    pub fn n(&self) -> usize {
        self.num_input_gates + self.num_aux_gates
    }

    fn add_gate_setup_polys_into_list<G: GateEquation>(&mut self, gate: &G) {
        let mut setup_index: Option<(&'static str, usize)> = None;
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::SetupPolynomial(name, idx, _) => {
                            setup_index = Some((name, *idx));
                        },
                        _ => {}
                    }

                    match setup_index.take() {
                        Some((name, idx)) => {
                            let key = PolyIdentifier::SetupPolynomial(name, idx);
                            self.sorted_setup_polynomial_ids.push(key);
                        },
                        _ => {}
                    }
                }
            }
        }
    }

    fn add_gate_into_list<G: GateEquation>(&mut self, gate: &G) {
        if !self.constraints.contains(gate.as_internal() as &dyn GateEquationInternal) {
            self.constraints.insert(gate.clone().into_internal());

            self.add_gate_setup_polys_into_list(gate);

            self.sorted_gates.push(gate.clone().into_internal());

            let degree = gate.degree();
            if self.max_constraint_degree < degree {
                self.max_constraint_degree = degree;
            }

            let gate_constants = G::output_constant_coefficients::<E>();
            self.sorted_gate_constants.push(gate_constants.clone());
            self.gate_internal_coefficients.0.insert(Box::from(gate.clone().into_internal()), gate_constants);
        }        
    }

    pub fn new() -> Self {
        let mut tmp = Self {
            inputs_storage: PolynomialStorage::new(),
            aux_storage: PolynomialStorage::new(),

            max_constraint_degree: 0,

            num_input_gates: 0,
            num_aux_gates: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            main_gate: MG::default(),

            trace_step_for_batch: None,

            constraints: std::collections::HashSet::new(),
            gate_internal_coefficients: GateConstantCoefficientsStorage::<E>::new(),

            aux_gate_density: GateDensityStorage::new(),
            sorted_setup_polynomial_ids: vec![],
            sorted_gates: vec![],
            sorted_gate_constants: vec![],

            is_finalized: false,

            _marker: std::marker::PhantomData
        };

        tmp.add_gate_into_list(&MG::default());

        assert!(check_gate_to_support_public_inputs(&tmp.main_gate), "default gate must support making public inputs");

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable() -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        if (self.n()+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        let dummmy = Self::get_dummy_variable();

        let empty_gate = MainGateTerm::<E>::new();
        let (vars, coeffs) = MG::format_term(empty_gate, dummmy).expect("must make empty padding gate");

        for _ in self.n()..(self.n().next_power_of_two() - 1) {
            self.new_single_gate_for_trace_step(
                MG::static_description(), 
                &coeffs, 
                &vars,
                &[]
            ).expect("must add padding gate");
        }

        assert!((self.n()+1).is_power_of_two());
        self.is_finalized = true;
    }

    fn get_storage_for_trace_step(&self, step: usize) -> &PolynomialStorage<E> {
        if step < self.num_input_gates {
            &self.inputs_storage
        } else {
            &self.aux_storage
        }
    }

    pub fn is_satisfied(&self) -> bool {
        // expect a small number of inputs

        // TODO: handle public inputs

        // for i in 0..self.num_input_gates {
        //     let gate = self.input_assingments
        // }

        let one = E::Fr::one();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let n = self.n() - 1;

        for (gate_type, density) in self.aux_gate_density.0.iter() {
            let constraints = gate_type.as_ref().get_constraints();
            let constants = self.gate_internal_coefficients.0.get(gate_type.as_ref()).expect(&format!("must get internal coefficients for the gate {:?}", gate_type.as_ref()));
            let mut constants_iter = constants.iter();

            for (gate_index, is_applicable) in density.iter().enumerate() {
                if is_applicable == false {
                    continue;
                }

                let trace_index = self.num_input_gates + gate_index;

                for constraint in constraints.iter() {
                    let mut constraint_value = E::Fr::zero();
                    for term in constraint.0.iter() {
                        let mut base = match term.0 {
                            Coefficient::PlusOne => one,
                            Coefficient::MinusOne => minus_one,
                            Coefficient::Other => *constants_iter.next().unwrap()
                        };

                        let storage = self.get_storage_for_trace_step(trace_index);

                        for poly in term.1.iter() {
                            let value = match poly {
                                PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(dilation)) => {
                                    debug_assert!(*dilation <= 1, "only handles variables on this and next step");
                                    if trace_index == n && *dilation > 0 {
                                        continue;
                                    }
                                    let variable = storage.get_variable(poly, gate_index).expect(&format!("must get a variable for poly {:?} for aux gate {}", poly, gate_index));
                                    let value = self.get_value(variable).expect("must get a state variable value");

                                    value
                                },
                                PolynomialInConstraint::SetupPolynomial(_, _, TimeDilation(dilation)) => {
                                    debug_assert_eq!(*dilation, 0, "only handles setup polys on this step for now");
                                    if trace_index == n && *dilation > 0 {
                                        continue;
                                    }

                                    let value = storage.get_value(poly, gate_index).expect(&format!("must get a setup value for poly {:?} for aux gate {}", poly, gate_index));
                                    
                                    value
                                },
                                PolynomialInConstraint::WitnessPolynomial(_, TimeDilation(dilation)) => {
                                    debug_assert_eq!(*dilation, 0, "only handles witness polys on this step for now");
                                    if trace_index == n && *dilation > 0 {
                                        continue;
                                    }

                                    let value = storage.get_value(poly, gate_index).expect(&format!("must get a witness value for poly {:?} for aux gate {}", poly, gate_index));
                                    
                                    value
                                }
                            };

                            base.mul_assign(&value);
                        }

                        constraint_value.add_assign(&base);
                    }

                    if !constraint_value.is_zero() {
                        println!("Unsatisfied at aux gate {} (zero enumerated)", gate_index);
                        println!("Constraint value = {}", constraint_value);
                        println!("Gate {:?}", gate_type);
                        return false;
                    }
                }
            }
        }

        true
    }

    pub(crate) fn make_permutations(&self, worker: &Worker) -> Vec<Polynomial::<E::Fr, Values>> {
        assert!(self.is_finalized);

        let num_gates = self.n();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        let mut poly_ids = vec![];
        for i in 0..P::STATE_WIDTH {
            let id = PolyIdentifier::VariablesPolynomial(i);
            poly_ids.push(id);
        }

        // gate_idx is zero-enumerated here
        for gate_idx in 0..num_gates
        {
            let storage = self.get_storage_for_trace_step(gate_idx);
            for (state_poly_index, poly_id) in poly_ids.iter().enumerate() {
                let variables_vec_ref = storage.state_map.get(&poly_id).expect("must get a variables polynomial");
                let storage_idx = if gate_idx < self.num_input_gates {
                    gate_idx
                } else {
                    gate_idx - self.num_input_gates
                };

                let v = variables_vec_ref[storage_idx];
                match v {
                    Variable(Index::Aux(0)) => {
                        // Dummy variables do not participate in the permutation
                    },
                    Variable(Index::Input(0)) => {
                        unreachable!("There must be no input with index 0");
                    },
                    Variable(Index::Input(index)) => {
                        let i = index; // inputs are [1, num_inputs]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                    Variable(Index::Aux(index)) => {
                        let i = index + num_inputs; // aux are [num_inputs + 1, ..]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                }
            }
        }

        // sanity check
        assert_eq!(partitions[0].len(), 0);

        let domain = Domain::new_for_size(num_gates as u64).expect("must have enough roots of unity to fit the circuit");

        // now we need to make root at it's cosets
        let domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, &worker
        );

        // domain_elements.pop().unwrap();

        use crate::ff::SqrtField;
        use crate::ff::LegendreSymbol;

        let mut non_residues = vec![];
        non_residues.push(E::Fr::one());
        non_residues.extend(make_non_residues::<E::Fr>(P::STATE_WIDTH - 1));

        assert_eq!(non_residues.len(), 4);

        let mut sigmas = vec![];
        for i in 0..P::STATE_WIDTH {
            let mut sigma_i = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
            sigma_i.scale(&worker, non_residues[i]);
            sigmas.push(sigma_i);
        }

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate<T: Sized>(mut vec: Vec<T>) -> Vec<T> {
            if vec.len() > 1 {
                let mut els: Vec<_> = vec.drain(0..1).collect();
                els.reverse();
                vec.push(els.pop().unwrap());
            }

            vec
        }

        for (i, partition) in partitions.into_iter().enumerate().skip(1) {
            // copy-permutation should have a cycle around the partition

            // we do not need to permute over partitions of length 1,
            // as this variable only happends in one place
            if partition.len() == 1 {
                continue;
            }

            let permutation = rotate(partition.clone());
            permutations[i] = permutation.clone();

            // let permutation = partition.clone();
            // permutations[i] = permutation;

            for (original, new) in partition.into_iter()
                                    .zip(permutation.into_iter()) 
            {
                // (column_idx, trace_step_idx)
                let new_zero_enumerated = new.1 - 1;
                let mut new_value = domain_elements[new_zero_enumerated];

                // we have shuffled the values, so we need to determine FROM
                // which of k_i * {1, omega, ...} cosets we take a value
                // for a permutation polynomial
                new_value.mul_assign(&non_residues[new.0]);

                // check to what witness polynomial the variable belongs
                let place_into = &mut sigmas[original.0].as_mut();

                let original_zero_enumerated = original.1 - 1;
                place_into[original_zero_enumerated] = new_value;
            }
        }

        sigmas
    }

    pub fn perform_setup(
        &self, 
        worker: &Worker
    ) -> Result<
    (std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, Vec<Polynomial<E::Fr, Values>>), 
    SynthesisError
    > {
        assert!(self.is_finalized);
        let total_num_gates = self.n();

        let num_input_gates = self.num_input_gates;

        let mut map = std::collections::HashMap::new();

        let setup_poly_ids: Vec<_> = self.aux_storage.setup_map.keys().collect();

        for &id in setup_poly_ids.into_iter() {
            let mut assembled_poly = vec![E::Fr::zero(); total_num_gates];
            if num_input_gates != 0 {
                let input_gates_coeffs = &mut assembled_poly[..num_input_gates];
                input_gates_coeffs.copy_from_slice(&self.inputs_storage.setup_map.get(&id).unwrap()[..]);
            }

            {
                let aux_gates_coeffs = &mut assembled_poly[num_input_gates..];
                aux_gates_coeffs.copy_from_slice(&self.aux_storage.setup_map.get(&id).unwrap()[..]);
            }

            let as_poly = Polynomial::from_values_unpadded(assembled_poly)?;

            map.insert(id, as_poly);
        }

        let permutation_polys = self.make_permutations(&worker);

        Ok((map, permutation_polys))
    }

    pub fn output_gate_selectors(&self, worker: &Worker) -> Result<Vec<Polynomial<E::Fr, Values>>, SynthesisError> {
        assert!(self.is_finalized);
        if self.sorted_gates.len() == 1 {
            return Ok(vec![]);
        }

        let num_gate_selectors = self.sorted_gates.len();

        let one = E::Fr::one();
        let empty_poly = Polynomial::<E::Fr, Values>::new_for_size(self.n().next_power_of_two())?;
        let mut poly_values = vec![empty_poly.clone(); num_gate_selectors];
        let num_input_gates = self.num_input_gates;

        for p in poly_values.iter_mut() {
            for p in p.as_mut()[..num_input_gates].iter_mut() {
                *p = one;
            }
        }

        worker.scope(poly_values.len(), |scope, chunk| {
            for (i, lh) in poly_values.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = &self.sorted_gates[idx];
                        let density = self.aux_gate_density.0.get(id).unwrap();
                        let poly_mut_slice: &mut [E::Fr] = &mut lh.as_mut()[num_input_gates..];
                        for (i, d) in density.iter().enumerate() {
                            if d {
                                poly_mut_slice[i] = one;
                            }
                        }
                    }
                });
            }
        });

        Ok(poly_values)
    }

    pub fn make_state_and_witness_polynomials(
        &self,
        worker: &Worker
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<Vec<E::Fr>>), SynthesisError>
    {
        assert!(self.is_finalized);

        let mut full_assignments = vec![Vec::with_capacity((self.n()+1).next_power_of_two()); P::STATE_WIDTH];

        let num_input_gates = self.num_input_gates;
        let num_aux_gates = self.num_aux_gates;

        full_assignments[0].extend_from_slice(&self.input_assingments);
        assert!(full_assignments[0].len() == num_input_gates);
        for i in 1..P::STATE_WIDTH {
            full_assignments[i].resize(num_input_gates, E::Fr::zero());
        }

        worker.scope(full_assignments.len(), |scope, chunk| {
            for (i, lh) in full_assignments.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = PolyIdentifier::VariablesPolynomial(idx);
                        let poly_ref = self.aux_storage.state_map.get(&id).unwrap();
                        for i in 0..num_aux_gates {
                            let var = poly_ref[i];
                            let value = self.get_value(var).unwrap();
                            lh.push(value);
                        }
                    }
                });
            }
        });

        for p in full_assignments.iter_mut() {
            p.resize((self.n()+1).next_power_of_two() - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), (self.n()+1).next_power_of_two() - 1);
        }

        Ok((full_assignments, vec![]))
    }
}

use crate::pairing::bn256;

#[cfg(feature = "redshift")]
pub fn prove_with_rescue_bn256<P: PlonkConstraintSystemParams<bn256::Bn256>, MG: MainGateEquation, C: Circuit<bn256::Bn256>>(
    circuit: &C
) -> Result<(), SynthesisError> {
    use super::*;
    use rescue_hash::RescueEngine;
    use rescue_hash::bn256::Bn256RescueParams;

    use super::redshift::setup::*;
    use super::redshift::prover::*;
    use super::redshift::tree_hash::*;

    use crate::worker::Worker;

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    println!("Performing setup for {} gates", num_gates);

    let params = Bn256RescueParams::new_checked_2_into_1(); 

    use crate::plonk::commitments::transcript::{Prng, rescue_transcript};

    let mut prng = rescue_transcript::RescueTranscript::<bn256::Bn256>::from_params(&params);

    let hasher = RescueBinaryTreeHasher::<bn256::Bn256>::new(&params);

    let worker = Worker::new();

    let (setup_multioracle, mut permutations) = SetupMultioracle::from_assembly(
        assembly,
        hasher.clone(),
        &worker
    )?;

    println!("Setup is done");

    // cut permutations
    for p in permutations.iter_mut() {
        p.pop_last().unwrap();
    }

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    let start = std::time::Instant::now();

    let (prover, first_state, first_message) = RedshiftProver::first_step(
        assembly, 
        hasher.clone(), 
        &worker
    )?;

    println!("First message");

    for input in first_message.input_values.iter() {
        prng.commit_input(input);
    }

    prng.commit_input(&first_message.witness_multioracle_commitment);

    let beta = prng.get_challenge();
    let gamma = prng.get_challenge();

    let first_verifier_message = FirstVerifierMessage::<bn256::Bn256> {
        beta,
        gamma,
    };

    let (second_state, second_message) = prover.second_step_from_first_step(
        first_state, 
        first_verifier_message, 
        &permutations, 
        &worker
    )?;

    println!("Second message");

    prng.commit_input(&second_message.grand_product_oracle_commitment);

    let alpha = prng.get_challenge();

    let second_verifier_message = SecondVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
    };

    let (third_state, third_message) = prover.third_step_from_second_step(
        second_state, 
        second_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Third message");

    prng.commit_input(&third_message.quotient_poly_oracle_commitment);

    let z = prng.get_challenge();

    let third_verifier_message = ThirdVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
    };

    let (fourth_state, fourth_message) = prover.fourth_step_from_third_step(
        third_state, 
        third_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Fourth message");

    let mut wire_values_at_z = fourth_message.wire_values_at_z;
    wire_values_at_z.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z: Vec<_> = wire_values_at_z.into_iter().map(|el| el.1).collect();

    let mut wire_values_at_z_omega = fourth_message.wire_values_at_z_omega;
    wire_values_at_z_omega.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z_omega: Vec<_> = wire_values_at_z_omega.into_iter().map(|el| el.1).collect();

    for w in wire_values_at_z.iter()
        .chain(&wire_values_at_z_omega)
        .chain(&Some(fourth_message.grand_product_at_z))
        .chain(&Some(fourth_message.grand_product_at_z_omega))
        .chain(&fourth_message.quotient_polynomial_parts_at_z)
        .chain(&fourth_message.setup_values_at_z)
        .chain(&fourth_message.permutation_polynomials_at_z)
        .chain(&fourth_message.gate_selector_polynomials_at_z) 
    {
        prng.commit_input(&w);
    }

    let v = prng.get_challenge();

    let fourth_verifier_message = FourthVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
        v,
    };

    let fifth_message = prover.fifth_step_from_fourth_step(
        fourth_state, 
        fourth_verifier_message, 
        &setup_multioracle, 
        &mut prng,
        &worker
    )?;

    println!("Fifth message");

    println!("Proving {} gates taken {:?}", num_gates, start.elapsed());

    Ok(())
}

#[cfg(feature = "redshift")]
pub fn prove_with_poseidon_bn256<P: PlonkConstraintSystemParams<bn256::Bn256>, MG: MainGateEquation, C: Circuit<bn256::Bn256>>(
    circuit: &C
) -> Result<(), SynthesisError> {
    use super::*;
    use poseidon_hash::PoseidonEngine;
    use poseidon_hash::bn256::Bn256PoseidonParams;

    use super::redshift::setup::*;
    use super::redshift::prover::*;
    use super::redshift::tree_hash::*;

    use crate::worker::Worker;

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    println!("Performing setup for {} gates", num_gates);

    let params = Bn256PoseidonParams::new_checked_2_into_1(); 

    use crate::plonk::commitments::transcript::{Prng, poseidon_transcript};

    let mut prng = poseidon_transcript::PoseidonTranscript::<bn256::Bn256>::from_params(&params);

    let hasher = PoseidonBinaryTreeHasher::<bn256::Bn256>::new(&params);

    let worker = Worker::new();

    let (setup_multioracle, mut permutations) = SetupMultioracle::from_assembly(
        assembly,
        hasher.clone(),
        &worker
    )?;

    println!("Setup is done");

    // cut permutations
    for p in permutations.iter_mut() {
        p.pop_last().unwrap();
    }

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    let start = std::time::Instant::now();

    let (prover, first_state, first_message) = RedshiftProver::first_step(
        assembly, 
        hasher.clone(), 
        &worker
    )?;

    println!("First message");

    for input in first_message.input_values.iter() {
        prng.commit_input(input);
    }

    prng.commit_input(&first_message.witness_multioracle_commitment);

    let beta = prng.get_challenge();
    let gamma = prng.get_challenge();

    let first_verifier_message = FirstVerifierMessage::<bn256::Bn256> {
        beta,
        gamma,
    };

    let (second_state, second_message) = prover.second_step_from_first_step(
        first_state, 
        first_verifier_message, 
        &permutations, 
        &worker
    )?;

    println!("Second message");

    prng.commit_input(&second_message.grand_product_oracle_commitment);

    let alpha = prng.get_challenge();

    let second_verifier_message = SecondVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
    };

    let (third_state, third_message) = prover.third_step_from_second_step(
        second_state, 
        second_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Third message");

    prng.commit_input(&third_message.quotient_poly_oracle_commitment);

    let z = prng.get_challenge();

    let third_verifier_message = ThirdVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
    };

    let (fourth_state, fourth_message) = prover.fourth_step_from_third_step(
        third_state, 
        third_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Fourth message");

    let mut wire_values_at_z = fourth_message.wire_values_at_z;
    wire_values_at_z.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z: Vec<_> = wire_values_at_z.into_iter().map(|el| el.1).collect();

    let mut wire_values_at_z_omega = fourth_message.wire_values_at_z_omega;
    wire_values_at_z_omega.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z_omega: Vec<_> = wire_values_at_z_omega.into_iter().map(|el| el.1).collect();

    for w in wire_values_at_z.iter()
        .chain(&wire_values_at_z_omega)
        .chain(&Some(fourth_message.grand_product_at_z))
        .chain(&Some(fourth_message.grand_product_at_z_omega))
        .chain(&fourth_message.quotient_polynomial_parts_at_z)
        .chain(&fourth_message.setup_values_at_z)
        .chain(&fourth_message.permutation_polynomials_at_z)
        .chain(&fourth_message.gate_selector_polynomials_at_z) 
    {
        prng.commit_input(&w);
    }

    let v = prng.get_challenge();

    let fourth_verifier_message = FourthVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
        v,
    };

    let fifth_message = prover.fifth_step_from_fourth_step(
        fourth_state, 
        fourth_verifier_message, 
        &setup_multioracle, 
        &mut prng,
        &worker
    )?;

    println!("Fifth message");

    println!("Proving {} gates taken {:?}", num_gates, start.elapsed());

    Ok(())
}

#[cfg(feature = "redshift")]
pub fn prove_with_hash_counting_bn256<P: PlonkConstraintSystemParams<bn256::Bn256>, MG: MainGateEquation, C: Circuit<bn256::Bn256>>(
    circuit: &C
) -> Result<(), SynthesisError> {
    use super::*;
    use rescue_hash::RescueEngine;
    use rescue_hash::bn256::Bn256RescueParams;

    use super::redshift::setup::*;
    use super::redshift::prover::*;
    use super::redshift::tree_hash::*;

    use crate::worker::Worker;

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    println!("Performing setup for {} gates", num_gates);

    let params = Bn256RescueParams::new_checked_2_into_1(); 

    use crate::plonk::commitments::transcript::{Prng, rescue_transcript};

    let mut prng = rescue_transcript::RescueTranscript::<bn256::Bn256>::from_params(&params);

    let hasher = CountingHash::<bn256::Bn256>::new();

    let worker = Worker::new();

    let (setup_multioracle, mut permutations) = SetupMultioracle::from_assembly(
        assembly,
        hasher.clone(),
        &worker
    )?;

    println!("Setup is done");

    // cut permutations
    for p in permutations.iter_mut() {
        p.pop_last().unwrap();
    }

    let mut assembly = TrivialAssembly::<bn256::Bn256, P, MG>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let num_gates = assembly.n();

    let start = std::time::Instant::now();

    let (prover, first_state, first_message) = RedshiftProver::first_step(
        assembly, 
        hasher.clone(), 
        &worker
    )?;

    println!("First message");

    for input in first_message.input_values.iter() {
        prng.commit_input(input);
    }

    prng.commit_input(&first_message.witness_multioracle_commitment);

    let beta = prng.get_challenge();
    let gamma = prng.get_challenge();

    let first_verifier_message = FirstVerifierMessage::<bn256::Bn256> {
        beta,
        gamma,
    };

    let (second_state, second_message) = prover.second_step_from_first_step(
        first_state, 
        first_verifier_message, 
        &permutations, 
        &worker
    )?;

    println!("Second message");

    prng.commit_input(&second_message.grand_product_oracle_commitment);

    let alpha = prng.get_challenge();

    let second_verifier_message = SecondVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
    };

    let (third_state, third_message) = prover.third_step_from_second_step(
        second_state, 
        second_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Third message");

    prng.commit_input(&third_message.quotient_poly_oracle_commitment);

    let z = prng.get_challenge();

    let third_verifier_message = ThirdVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
    };

    let (fourth_state, fourth_message) = prover.fourth_step_from_third_step(
        third_state, 
        third_verifier_message, 
        &setup_multioracle, 
        &worker
    )?;

    println!("Fourth message");

    let mut wire_values_at_z = fourth_message.wire_values_at_z;
    wire_values_at_z.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z: Vec<_> = wire_values_at_z.into_iter().map(|el| el.1).collect();

    let mut wire_values_at_z_omega = fourth_message.wire_values_at_z_omega;
    wire_values_at_z_omega.sort_by(|a, b| a.0.cmp(&b.0));

    let wire_values_at_z_omega: Vec<_> = wire_values_at_z_omega.into_iter().map(|el| el.1).collect();

    for w in wire_values_at_z.iter()
        .chain(&wire_values_at_z_omega)
        .chain(&Some(fourth_message.grand_product_at_z))
        .chain(&Some(fourth_message.grand_product_at_z_omega))
        .chain(&fourth_message.quotient_polynomial_parts_at_z)
        .chain(&fourth_message.setup_values_at_z)
        .chain(&fourth_message.permutation_polynomials_at_z)
        .chain(&fourth_message.gate_selector_polynomials_at_z) 
    {
        prng.commit_input(&w);
    }

    let v = prng.get_challenge();

    let fourth_verifier_message = FourthVerifierMessage::<bn256::Bn256> {
        alpha,
        beta,
        gamma,
        z,
        v,
    };

    let fifth_message = prover.fifth_step_from_fourth_step(
        fourth_state, 
        fourth_verifier_message, 
        &setup_multioracle, 
        &mut prng,
        &worker
    )?;

    println!("Fifth message");

    use std::sync::atomic::{AtomicUsize, Ordering};
    use super::redshift::tree_hash::COUNTER;

    let num_hashes = COUNTER.load(Ordering::Relaxed);

    println!("Num hash invocations: {}", num_hashes);

    Ok(())
}


#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;
    use crate::pairing::ff::PrimeField;

    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit4<E> {
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

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            // 2a - b = 0

            let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
            let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
            let mut term = MainGateTerm::new();
            term.add_assign(two_a);
            term.add_assign(minus_b);

            cs.allocate_main_gate(term)?;

            // c - a*b == 0 

            let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
            ab_term.scale(&negative_one);
            let c_term = ArithmeticTerm::from_variable(c);
            let mut term = MainGateTerm::new();
            term.add_assign(c_term);
            term.add_assign(ab_term);

            cs.allocate_main_gate(term)?;

            // d - 100 == 0 

            let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
            let d_term = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(d_term);
            term.sub_assign(hundred);

            cs.allocate_main_gate(term)?;

            let gamma = cs.alloc_input(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            // gamma - b == 0 

            let gamma_term = ArithmeticTerm::from_variable(gamma);
            let b_term = ArithmeticTerm::from_variable(b);
            let mut term = MainGateTerm::new();
            term.add_assign(gamma_term);
            term.sub_assign(b_term);

            cs.allocate_main_gate(term)?;

            // 2a
            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(a, two));

            let dummy = CS::get_dummy_variable();

            // 2a - d_next = 0

            let (vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            *coeffs.last_mut().unwrap() = negative_one;

            // here d is equal = 2a, so we need to place b there
            // and compensate it with -b somewhere before

            cs.new_single_gate_for_trace_step(CS::MainGate::static_description(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable(b));

            // b + 0 + 0 - b = 0
            let (mut vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            coeffs[3] = negative_one;
            vars[3] = b;

            cs.new_single_gate_for_trace_step(CS::MainGate::static_description(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit_with_gate_agnostic_cs() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.constraints.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} gates", assembly.n());
        
        assert!(assembly.is_satisfied());

        assembly.finalize();

        let worker = Worker::new();

        let (_storage, _permutation_polys) = assembly.perform_setup(&worker).unwrap();
    }

    #[test]
    #[cfg(feature = "redshift")]
    fn test_make_setup_for_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        use super::super::redshift::setup::*;
        use super::super::redshift::prover::*;
        use super::super::redshift::tree_hash::*;
        use rescue_hash::bn256::Bn256RescueParams;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.constraints.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} gates", assembly.n());
        
        assert!(assembly.is_satisfied());

        assembly.finalize();

        let params = Bn256RescueParams::new_checked_2_into_1();
        let hasher = RescueBinaryTreeHasher::<Bn256>::new(&params);

        let worker = Worker::new();

        let (setup_multioracle, mut permutations) = SetupMultioracle::from_assembly(
            assembly,
            hasher.clone(),
            &worker
        ).unwrap();

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assembly.finalize();

        let (prover, first_state, first_message) = RedshiftProver::first_step(
            assembly, 
            hasher.clone(), 
            &worker
        ).unwrap();

        let first_verifier_message = FirstVerifierMessage::<Bn256> {
            beta: Fr::from_str("123").unwrap(),
            gamma: Fr::from_str("456").unwrap(),
        };

        // cut permutations

        for p in permutations.iter_mut() {
            p.pop_last().unwrap();
        }

        let (second_state, second_message) = prover.second_step_from_first_step(
            first_state, 
            first_verifier_message, 
            &permutations, 
            &worker
        ).unwrap();

        let second_verifier_message = SecondVerifierMessage::<Bn256> {
            alpha: Fr::from_str("789").unwrap(),
            beta: Fr::from_str("123").unwrap(),
            gamma: Fr::from_str("456").unwrap(),
        };

        let (third_state, third_message) = prover.third_step_from_second_step(
            second_state, 
            second_verifier_message, 
            &setup_multioracle, 
            &worker
        ).unwrap();

        let third_verifier_message = ThirdVerifierMessage::<Bn256> {
            alpha: Fr::from_str("789").unwrap(),
            beta: Fr::from_str("123").unwrap(),
            gamma: Fr::from_str("456").unwrap(),
            z: Fr::from_str("1337").unwrap()
        };

        let (fourth_state, fourth_message) = prover.fourth_step_from_third_step(
            third_state, 
            third_verifier_message, 
            &setup_multioracle, 
            &worker
        ).unwrap();

        let fourth_verifier_message = FourthVerifierMessage::<Bn256> {
            alpha: Fr::from_str("789").unwrap(),
            beta: Fr::from_str("123").unwrap(),
            gamma: Fr::from_str("456").unwrap(),
            z: Fr::from_str("1337").unwrap(),
            v: Fr::from_str("97531").unwrap(),
        };

        use crate::plonk::commitments::transcript::{Prng, rescue_transcript};

        let mut prng = rescue_transcript::RescueTranscript::<Bn256>::from_params(&params);
        prng.commit_input(&Fr::from_str("97531").unwrap());

        let fifth_message = prover.fifth_step_from_fourth_step(
            fourth_state, 
            fourth_verifier_message, 
            &setup_multioracle, 
            &mut prng,
            &worker
        ).unwrap();
    }
}