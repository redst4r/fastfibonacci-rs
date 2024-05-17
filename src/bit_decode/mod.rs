//! This module contains the code for decoding Fibonacci encoding with a 
//! `bitvec::BitVec` backend, which handles most of the complexity of querying 
//! indifivudal bits in the stream.
//! 
pub mod fast;
pub mod fibonacci;

use bitvec::prelude as bv;

/// The type of bitvector used in the crate.
/// Importantly, some code *relies* on `Msb0`
pub(crate) type MyStore = u8;
pub (crate) type MyBitOrder = bv::Msb0;
/// bitslicie used in the crate
pub type MyBitSlice = bv::BitSlice<MyStore,MyBitOrder>;
/// reftype that goes with [`MyBitSlice`]
pub type MyBitVector = bv::BitVec<MyStore, MyBitOrder>;


/// Marker trait for Fibonacci decoders.
/// This is an iterator over u64 (the decoded integers),
/// and lets you return parts of the buffer not yet decoded.
pub trait FbDec<'a>: Iterator<Item = u64> {
    /// Returns the buffer behind the last bit processed.
    /// Comes handy when the buffer contains data OTHER than fibonacci encoded
    /// data that needs to be processed externally.
    fn get_remaining_buffer(&self) -> &'a MyBitSlice;

    /// how far did we process into the buffer (pretty much the first bit after a 11).
    fn get_bits_processed(&self) -> usize;
}