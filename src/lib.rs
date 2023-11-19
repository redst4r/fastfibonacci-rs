//! # fastfibonacci
//!
//! Fibonacci encoding of integers, either regular (bit by bit) or decoding in chunks.
//!
//! ## Regular encoding and decoding:
//! ```rust
//! use fastfibonacci::fibonacci::{encode,FibonacciDecoder};
//! let encoded = encode(&vec![34, 12]) ;
//!
//! // 2nd argument: shift all values by -1 (in case we wanted to encode 0 in the fibonacci encoding)
//! let f = FibonacciDecoder::new(&encoded, false);
//! assert_eq!(f.collect::<Vec<_>>(), vec![34,12])
//! ```
//!
//! ## Fast decoding:
//! 1. Create a LookupTable first (expensive), which decodes multiple bits in a chunk.
//!    Currently, we provide [`LookupU8Vec`] (decoding 8bits at a time) and [`LookupU16Vec`] (decoding 16 bits).
//! 2. The lookup table can then be used to do any amount if decoding.
//!
//! ```rust
//! use fastfibonacci::fibonacci_fast::{fast_decode_u8,fast_decode_u16, LookupU8Vec, LookupU16Vec };
//! use bitvec::prelude as bv;
//! let bits = bv::bits![u8, bv::Msb0;
//!     1,0,1,1,0,1,0,1,
//!     1,0,1,0,0,1,0,1,
//!     0,1,1,1,0,0,1,0].to_bitvec();
//! // using a u8 lookup table
//! let table = LookupU8Vec::new();
//! let r = fast_decode_u8(bits.clone(), &table);
//! assert_eq!(r, vec![4,7, 86]);
//!
//! // using a u16 table
//! let table = LookupU16Vec::new();
//! let r = fast_decode_u16(bits.clone(), &table);
//! assert_eq!(r, vec![4,7, 86]);
//! ```
pub mod fibonacci;
pub mod fibonacci_fast;
pub mod fibonacci_old;
mod utils;
pub use utils::random_fibonacci_stream;

use bitvec::prelude as bv;

/// The type of bitvector used in the crate.
/// Importantly, some code *relies* on `Msb0`
pub(crate) type MyBitSlice = bv::BitSlice<u8, bv::Msb0>;
/// reftype thqt goes with [`MyBitSlice`]
pub(crate) type MyBitVector = bv::BitVec<u8, bv::Msb0>;


/// Marker trait for Fibonacci decoders.
/// This is an iterator over u64 (the decoded integers),
/// and lets you return parts of the buffer not yet decoded
pub trait FbDec<'a>: Iterator<Item = u64> {
    /// Returns the buffer behind the last bit processed.
    /// Comes handy when the buffer contains data OTHER than fibonacci encoded
    /// data that needs to be processed externally.
    fn get_remaining_buffer(&self) -> &'a MyBitSlice;

    /// how far did we process into the buffer (pretty much the first bit after a 11).
    fn get_bits_processed(&self) -> usize;
}