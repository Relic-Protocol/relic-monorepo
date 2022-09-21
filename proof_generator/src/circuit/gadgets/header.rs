use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::plonk::circuit::byte::Byte;

use super::VarVec;
use super::variable_keccak::{KeccakDigest, KeccakGadget};

pub const MIN_HEADER_SIZE: usize = 500;
pub const MAX_HEADER_SIZE: usize = 679;

pub const STATE_ROOT_OFFSET: usize = 0x5B;

pub type BlockHeaderHasher<E> = KeccakGadget<E, MIN_HEADER_SIZE, MAX_HEADER_SIZE>;
pub type BlockHeaderVec<E> = VarVec<E, Byte<E>, MAX_HEADER_SIZE>;

pub fn extract_state_root<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    header: &BlockHeaderVec<E>
) -> Result<KeccakDigest<E>, SynthesisError> {
    KeccakDigest::from_le_bytes(cs, &header.vals[STATE_ROOT_OFFSET..STATE_ROOT_OFFSET+32])
}
