use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use super::affine_point_wrapper::*;

use franklin_crypto::bellman::SynthesisError;

use franklin_crypto::bellman::pairing::ff::*;

pub fn allocated_num_to_aligned_big_endian<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, None)?;
    assert!(bits.len() < 256);

    bits.resize(256, Boolean::constant(false));
    bits.reverse();

    Ok(bits)
}

pub fn serialize_point_into_big_endian<'a, E: Engine, CS: ConstraintSystem<E>, WP: WrappedAffinePoint<'a, E>>(
    cs: &mut CS,
    point: &WP
) -> Result<Vec<Boolean>, SynthesisError> {
    let raw_point = point.get_point();

    let x = raw_point.get_x().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;
    let y = raw_point.get_y().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;

    let mut serialized = vec![];

    for coord in vec![x, y].into_iter() {
        for limb in coord.into_limbs().into_iter() {
            let as_num = limb.into_variable(); // this checks coeff and constant term internally
            serialized.extend(allocated_num_to_aligned_big_endian(cs, &as_num)?);
        }
    }

    Ok(serialized)
}

pub fn bytes_to_keep<E: Engine>() -> usize {
        (E::Fr::CAPACITY / 8) as usize
}

pub fn add_scalar_field_elements<E: Engine>(src: &[AllocatedNum<E>], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        let num = Num::Variable(el.clone());
        dst.push(num);
    }
}

pub fn add_prime_field_elements<'a, E: Engine, F: PrimeField>(src: &[FieldElement<'a, E, F>], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        for limb in el.binary_limbs.iter() {
            let as_num = limb.term.into_num();
            dst.push(as_num);
        }        
    }
}

pub fn add_wp_points<'a, E: Engine, WP: WrappedAffinePoint<'a, E>>(src: &[WP], dst: &mut Vec<Num<E>>) {
    for el in src.iter() {
        let p = el.get_point();
        let x = p.x.clone();
        let y = p.y.clone();
        add_prime_field_elements(&[x, y], dst);   
    }
}

fn field_to_witness<E: Engine, F: PrimeField>(element: &F, params: &RnsParameters<E, F>) -> Vec<E::Fr> {
    if params.can_allocate_from_double_limb_witness() {
        let mut num_witness = params.num_limbs_for_in_field_representation / 2;
        if params.num_limbs_for_in_field_representation % 2 != 0 {
            num_witness += 1;
        }

        let coord_as_bigint = fe_to_biguint(element);

        let witness_limbs = split_into_fixed_number_of_limbs(
            coord_as_bigint, 
            params.binary_limbs_params.limb_size_bits * 2, 
            num_witness
        );

        let witnesses: Vec<_> = witness_limbs.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();

        witnesses
    } else {
        let num_witness = params.num_limbs_for_in_field_representation;

        let coord_as_bigint = fe_to_biguint(element);

        let witness_limbs = split_into_fixed_number_of_limbs(
            coord_as_bigint, 
            params.binary_limbs_params.limb_size_bits, 
            num_witness
        );

        let witnesses: Vec<_> = witness_limbs.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();

        witnesses
    }
}

pub fn add_ff_point<E: Engine>(src: &E::G1Affine, dst: &mut Vec<E::Fr>, params: &RnsParameters<E, <E::G1Affine as GenericCurveAffine>::Base>) {
    assert!(!<E::G1Affine as CurveAffine>::is_zero(src));
    let (x, y) = <E::G1Affine as CurveAffine>::into_xy_unchecked(*src);

    for coord in [x, y].iter() {
        let w = field_to_witness(coord, params);
        dst.extend(w);
    }
}

pub fn add_field_element<F: PrimeField>(src: &F, dst: &mut Vec<u8>) {
    let repr = src.into_repr();

    let mut buffer = [0u8; 32];
    repr.write_be(&mut buffer[..]).expect("must write");

    dst.extend_from_slice(&buffer);
}

pub fn add_point<E: Engine>(src: &E::G1Affine, dst: &mut Vec<u8>, params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>) {
    let mut tmp_dest = vec![];
    decompose_point_into_limbs(src, &mut tmp_dest, params);

    for p in tmp_dest.into_iter() {
        add_field_element(&p, dst);
    }
}

pub fn decompose_point_into_limbs<E: Engine>(src: &E::G1Affine, dst: &mut Vec<E::Fr>, params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>) {
    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);

    let params = &new_params;

    add_ff_point(src, dst, &params);
}
