use crate::pairing::ff::PrimeField;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::polynomials::*;
use crate::worker::*;
use crate::SynthesisError;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::commitments::transparent::utils::log2_floor;
use crate::plonk::commitments::transcript::Prng;
use crate::plonk::commitments::transparent::precomputations::*;
use super::super::*;

pub struct NaiveFriIop<F: PrimeField, I: IOP<F>> {
    _marker_f: std::marker::PhantomData<F>,
    _marker_i: std::marker::PhantomData<I>,
}

impl<F: PrimeField, I: IOP<F> > FriIop<F> for NaiveFriIop<F, I> {
    const DEGREE: usize = 2;

    type IopType = I;
    type ProofPrototype = FRIProofPrototype<F, I>;
    type Proof = FRIProof<F, I>;
    type Params = ();

    fn proof_from_lde<P: Prng<F, Input = < < I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F> >::HashOutput>,
        C: FriPrecomputations<F>
    >(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &C,
        worker: &Worker,
        prng: &mut P,
        params: &Self::Params
    ) -> Result<Self::ProofPrototype, SynthesisError> {
        NaiveFriIop::proof_from_lde_by_values(
            lde_values, 
            lde_factor,
            output_coeffs_at_degree_plus_one,
            precomputations,
            worker,
            prng
        )
    }

    fn prototype_into_proof(
        prototype: Self::ProofPrototype,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_indexes: Vec<usize>,
        _params: &Self::Params
    ) -> Result<Self::Proof, SynthesisError> {
        prototype.produce_proof(iop_values, natural_first_element_indexes)
    }

    fn get_fri_challenges<P: Prng<F, Input = < < I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F> >::HashOutput> >(
        proof: &Self::Proof,
        prng: &mut P,
        _params: &Self::Params
    ) -> Vec<F> {
        let mut fri_challenges = vec![];

        for root in proof.roots.iter() {
            let iop_challenge = {
                prng.commit_input(&root);
                prng.get_challenge()
            };

            fri_challenges.push(iop_challenge);
        }

        fri_challenges
    }

    fn verify_proof_with_challenges(
        proof: &Self::Proof,
        natural_element_indexes: Vec<usize>,
        expected_value: &[F],
        fri_challenges: &[F],
        _params: &Self::Params
    ) -> Result<bool, SynthesisError> {
        Self::verify_proof_queries(proof, natural_element_indexes, Self::DEGREE, expected_value, fri_challenges)
    }
}

use std::time::Instant;

#[derive(PartialEq, Eq, Clone)]
pub struct FRIProofPrototype<F: PrimeField, I: IOP<F>> {
    pub l0_commitment: I,
    pub intermediate_commitments: Vec<I>,
    pub intermediate_values: Vec< Polynomial<F, Values> >,
    pub challenges: Vec<F>,
    pub final_root: < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput,
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one: usize,
    pub output_coeffs_at_degree_plus_one: usize,
    pub lde_factor: usize,
}

impl<F: PrimeField, I: IOP<F>> FriProofPrototype<F, I> for FRIProofPrototype<F, I> {
    fn get_roots(&self) -> Vec< < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput> {
        let mut roots = vec![];
        roots.push(self.l0_commitment.get_root().clone());
        for c in self.intermediate_commitments.iter() {
            roots.push(c.get_root().clone());
        }

        roots
    }

    fn get_final_root(&self) -> < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput {
        self.final_root.clone()
    }

    fn get_final_coefficients(&self) -> Vec<F> {
        self.final_coefficients.clone()
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct FRIProof<F: PrimeField, I: IOP<F>> {
    pub queries: Vec< Vec< <I as IOP<F> >::Query > >,
    pub roots: Vec< < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput>,
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one: usize,
    pub output_coeffs_at_degree_plus_one: usize,
    pub lde_factor: usize,
}

impl<F: PrimeField, I: IOP<F>> FriProof<F, I> for FRIProof<F, I> {
    fn get_final_coefficients(&self) -> &[F] {
        &self.final_coefficients
    }
}

impl<F: PrimeField, I: IOP<F>> NaiveFriIop<F, I> {
    pub fn proof_from_lde_through_coefficients<P: Prng<F, Input = < < I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F> >::HashOutput> >(
        lde_values: Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        worker: &Worker,
        prng: &mut P
    ) -> Result<FRIProofPrototype<F, I>, SynthesisError> {
        let l0_commitment: I = I::create(lde_values.as_ref());
        let initial_domain_size = lde_values.size();

        assert!(output_coeffs_at_degree_plus_one.is_power_of_two());
        assert!(lde_factor.is_power_of_two());

        let initial_degree_plus_one = initial_domain_size / lde_factor;
        let num_steps = log2_floor(initial_degree_plus_one / output_coeffs_at_degree_plus_one) as usize;

        let initial_polynomial = lde_values.ifft(&worker);
        let mut initial_polynomial_coeffs = initial_polynomial.into_coeffs();
        initial_polynomial_coeffs.truncate(initial_degree_plus_one);
        
        let mut intermediate_commitments = vec![];
        let mut intermediate_values = vec![];
        let mut challenges = vec![];
        let mut next_domain_challenge = {
            prng.commit_input(&l0_commitment.get_root());
            prng.get_challenge()
        };
        challenges.push(next_domain_challenge);
        let mut next_domain_size = initial_polynomial_coeffs.len() / 2;

        let mut coeffs = initial_polynomial_coeffs;
        let mut roots = vec![];
        
        for step in 0..num_steps {
            let mut next_coefficients = vec![F::zero(); next_domain_size];
            let coeffs_slice: &[F] = coeffs.as_ref();
            assert!(next_coefficients.len()*2 == coeffs_slice.len());

            worker.scope(next_coefficients.len(), |scope, chunk| {
                for (v, old) in next_coefficients.chunks_mut(chunk)
                                .zip(coeffs_slice.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        for (v, old) in v.iter_mut().zip(old.chunks(2)) {
                            // a_0 + beta * a_1

                            let x = old[0];
                            let mut tmp = old[1];
                            tmp.mul_assign(&next_domain_challenge);
                            tmp.add_assign(&x);

                            *v = tmp;
                        }
                    });
                }
            });

            let next_coeffs_as_poly = Polynomial::from_coeffs(next_coefficients.clone())?;
            let next_values_as_poly = next_coeffs_as_poly.lde(&worker, lde_factor)?;
            let intermediate_iop = I::create(next_values_as_poly.as_ref());
            if step < num_steps - 1 {
                let root = intermediate_iop.get_root();
                roots.push(root);
                next_domain_challenge = {
                    prng.commit_input(&intermediate_iop.get_root());
                    prng.get_challenge()
                };

                challenges.push(next_domain_challenge);

                next_domain_size /= 2;

                intermediate_commitments.push(intermediate_iop);
                intermediate_values.push(next_values_as_poly);

                coeffs = next_coefficients;
            }
        }

        // challenges.pop().expect("will work");

        // let final_root = roots.pop().expect("will work");
        let final_root = roots.last().expect("will work").clone();

        assert!(challenges.len() == num_steps);
        assert!(intermediate_commitments.len() == num_steps);
        assert!(intermediate_values.len() == num_steps);

        let final_poly_coeffs = coeffs;

        assert!(final_poly_coeffs.len() == output_coeffs_at_degree_plus_one);

        Ok(FRIProofPrototype {
            l0_commitment,
            intermediate_commitments,
            intermediate_values,
            challenges,
            final_root,
            final_coefficients: final_poly_coeffs,
            initial_degree_plus_one,
            output_coeffs_at_degree_plus_one,
            lde_factor,
        })

    }

    pub fn proof_from_lde_by_values<P: Prng<F, Input = < < I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F> >::HashOutput>,
        C: FriPrecomputations<F>
    >(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &C,
        worker: &Worker,
        prng: &mut P
    ) -> Result<FRIProofPrototype<F, I>, SynthesisError> {
        println!("Starting FRI");
        let start = Instant::now();

        let mut roots = vec![];
        let l0_commitment: I = I::create(lde_values.as_ref());
        let root = l0_commitment.get_root();
        roots.push(root);
        let initial_domain_size = lde_values.size();

        assert_eq!(precomputations.domain_size(), initial_domain_size);

        let mut two = F::one();
        two.double();
        let two_inv = two.inverse().expect("should exist");
        
        assert!(output_coeffs_at_degree_plus_one.is_power_of_two());
        assert!(lde_factor.is_power_of_two());

        let initial_degree_plus_one = initial_domain_size / lde_factor;

        let num_steps = log2_floor(initial_degree_plus_one / output_coeffs_at_degree_plus_one) as usize;

        let mut intermediate_commitments = vec![];
        let mut intermediate_values = vec![];
        let mut challenges = vec![];
        let mut next_domain_challenge = {
            prng.commit_input(&l0_commitment.get_root());
            prng.get_challenge()
        };
        challenges.push(next_domain_challenge);

        let mut next_domain_size = initial_domain_size / 2;

        let mut values_slice = lde_values.as_ref();

        let omegas_inv_ref: &[F] = precomputations.omegas_inv_ref();

        // step 0: fold totally by 2
        // step 1: fold totally by 4
        // etc...
        
        for i in 0..num_steps {
            // we step over 1, omega, omega^2, 
            // then over 1, omega^2,
            // etc.
            let stride = 1 << i;
            let mut next_values = vec![F::zero(); next_domain_size];

            assert!(values_slice.len() == next_values.len() * 2);

            worker.scope(next_values.len(), |scope, chunk| {
                for (i, v) in next_values.chunks_mut(chunk).enumerate() {
                    scope.spawn(move |_| {
                        let initial_k = i*chunk;
                        for (j, v) in v.iter_mut().enumerate() {
                            let idx = initial_k + j;
                            debug_assert!(idx < next_domain_size);
                            let omega_idx = idx * stride;
                            let f_at_omega = values_slice[idx];
                            let f_at_minus_omega = values_slice[idx + next_domain_size];

                            let mut v_even_coeffs = f_at_omega;
                            v_even_coeffs.add_assign(&f_at_minus_omega);

                            let mut v_odd_coeffs = f_at_omega;
                            v_odd_coeffs.sub_assign(&f_at_minus_omega);
                            v_odd_coeffs.mul_assign(&omegas_inv_ref[omega_idx]);

                            // those can be treated as (doubled) evaluations of polynomials that
                            // are themselves made only from even or odd coefficients of original poly 
                            // (with reduction of degree by 2) on a domain of the size twice smaller
                            // with an extra factor of "omega" in odd coefficients

                            // to do assemble FRI step we just need to add them with a random challenge

                            let mut tmp = v_odd_coeffs;
                            tmp.mul_assign(&next_domain_challenge);
                            tmp.add_assign(&v_even_coeffs);
                            tmp.mul_assign(&two_inv);

                            *v = tmp;
                        }
                    });
                }
            });

            if i < num_steps - 1 {
                let intermediate_iop = I::create(next_values.as_ref());
                let root = intermediate_iop.get_root();
                roots.push(root);
                next_domain_challenge = {
                    prng.commit_input(&intermediate_iop.get_root());
                    prng.get_challenge()
                };
                challenges.push(next_domain_challenge);
                next_domain_size >>= 1;

                intermediate_commitments.push(intermediate_iop);
            } 

            let next_values_as_poly = Polynomial::from_values(next_values)?;
            intermediate_values.push(next_values_as_poly);

            values_slice = intermediate_values.last().expect("is something").as_ref();      
        }

        let final_root = roots.last().expect("will work").clone();

        assert_eq!(challenges.len(), num_steps);
        assert_eq!(roots.len(), num_steps);
        assert_eq!(intermediate_commitments.len(), num_steps-1);
        assert_eq!(intermediate_values.len(), num_steps);

        let final_poly_values = Polynomial::from_values(values_slice.to_vec())?;
        let final_poly_coeffs = final_poly_values.ifft(&worker);

        let mut final_poly_coeffs = final_poly_coeffs.into_coeffs();

        let mut degree = final_poly_coeffs.len() - 1;
        for c in final_poly_coeffs.iter().rev() {
            if c.is_zero() {
                degree -= 1;
            } else {
                break
            }
        }

        assert!(degree < output_coeffs_at_degree_plus_one, "polynomial degree is too large, coeffs = {:?}", final_poly_coeffs);

        final_poly_coeffs.truncate(output_coeffs_at_degree_plus_one);

        println!("Done FRI for degree {} in {:?}", lde_values.size()/lde_factor, start.elapsed());

        Ok(FRIProofPrototype {
            l0_commitment,
            intermediate_commitments,
            intermediate_values,
            challenges,
            final_root,
            final_coefficients: final_poly_coeffs,
            initial_degree_plus_one,
            output_coeffs_at_degree_plus_one,
            lde_factor,
        })

    }
}