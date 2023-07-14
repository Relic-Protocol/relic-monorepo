use franklin_crypto::plonk::circuit::byte::Byte;
use super::trie::SecureMPTGadget;
use super::VarVecN;

pub const ADDRESS_SIZE: usize = 20;
pub const ACCOUNT_NODE_MAX_SIZE: usize = 560;

// TODO: verify this
pub const ACCOUNT_TRIE_MAX_DEPTH: usize = 12;

pub type AccountTrieGadget<E> = SecureMPTGadget<E, ACCOUNT_TRIE_MAX_DEPTH, ACCOUNT_NODE_MAX_SIZE, ADDRESS_SIZE>;
pub type NodeVec<E> = VarVecN<E, Byte<E>, ACCOUNT_NODE_MAX_SIZE>;
pub type ProofVec<E> = VarVecN<E, NodeVec<E>, ACCOUNT_TRIE_MAX_DEPTH>;
