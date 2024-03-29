//! [Fibonacci encoding](https://en.wikipedia.org/wiki/Fibonacci_coding) of integers, 
//! either regular (bit by bit) or en/decoding in chunks via the 
//! [FastFibonacci encoding](https://ceur-ws.org/Vol-567/paper14.pdf) or 
//! [FastFibonacci decoding](https://www.semanticscholar.org/paper/Fast-data-Encoding-and-Deconding-Algorithms-Walder/4fbae5afc34dd32e7527fe4b1a1bd19e68794e3d) 
//! algorithm.
//!
//! ## Introduction
//! [Fibonacci encoding](https://en.wikipedia.org/wiki/Fibonacci_coding) is a variable-length encoding of integers, 
//! with the special property that any encoding of an interger ends in `1` (binary) and no encoding contains `11`. 
//! Hence one can use `11` as a separator in a stream of Fibonacci encoded integers.
//! 
//! Regular Fibonacci en/decoding works decoding bit by bit, which can be quite slow. 
//! [FastFibonacci decoding](https://www.semanticscholar.org/paper/Fast-data-Encoding-and-Deconding-Algorithms-Walder/4fbae5afc34dd32e7527fe4b1a1bd19e68794e3d)
//! looks at `n` bits at once, decoding this chunk in a single operation which can be faster.
//! 
//! # Examples
//! Regular encoding and decoding:
//! ```rust
//! use fastfibonacci::fibonacci::{encode, decode, FibonacciDecoder};
//! let encoded = encode(&vec![34, 12]) ;
//!
//! // Decoding
//! let decoded = decode(&encoded, false); // 2nd argument: shift all values by -1 (in case we wanted to encode 0 in the fibonacci encoding)
//! assert_eq!(decoded, vec![34,12]);
//! 
//! // Alternatively, we can also create an iterator (yields one decoded int at a time)
//! let f = FibonacciDecoder::new(&encoded, false);
//! assert_eq!(f.collect::<Vec<_>>(), vec![34,12])
//! ```
//!
//! Fast decoding:
//! 1. First, create an object implementing the [`fast::LookupTable`] trait (expensive), 
//!    which decodes multiple bits in a chunk.
//!    The crate provides the following implementations of the trait: 
//!     - [`fast::LookupVec<u8>`]: Decoding 8 bits at a time.
//!     - [`fast::LookupVec<u16>`]: Decoding 16 bits at a time.
//!    
//!     ***NOTE***:  There's also a (lazy) static version of this precomputed table via 
//!     - [`fast::FB_LOOKUP_U8`]
//!     - [`fast::FB_LOOKUP_U16`]
//!     which can be useful if the lookup table is needed in different places (but only calculated once)
//! 2. The lookup table can then be used to do any amount of decoding via a [`fast::FastFibonacciDecoder`].
//!    It's either instantiated 
//!     - explicitly via [`fast::FastFibonacciDecoder::new()`]
//!     - or via the helper functions [`fast::get_u8_decoder`], [`fast::get_u16_decoder`].
//! 
//!    ***Note***: For simplicity, there's also the [`fast::fast_decode`] function, which skips the Decoder and just immediately decodes the sequence.
//! 
//! ```rust
//! use fastfibonacci::fibonacci::encode;
//! use fastfibonacci::fast::{fast_decode,LookupVec, get_u8_decoder, get_u16_decoder};
//! use bitvec::prelude as bv;
//! let bits = encode(&vec![4,7, 86]) ;
//! // in bits, this is
//! // 10110101
//! // 10100101
//! // 0111;
//! 
//! // decoding all bits at once, using a u8 lookup table
//! let table8: LookupVec<u8> = LookupVec::new();
//! let r = fast_decode(&bits, false, &table8);
//! assert_eq!(r, vec![4,7, 86]);
//!
//! // decoding all bits at once, using a u16 table
//! let table16: LookupVec<u16> = LookupVec::new();
//! let r = fast_decode(&bits, false, &table16);
//! assert_eq!(r, vec![4,7, 86]);
//! 
//! // Getting an iterator over the decoded values
//! let dec8 = get_u8_decoder(&bits, false);
//! // or more explicitly, using the precomputed static table
//! // use fastfibonacci::fast::FB_LOOKUP_U8;
//! // let dec8 = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
//! assert_eq!(dec8.collect::<Vec<_>>(), vec![4,7, 86]);
//! 
//! let dec16 = get_u16_decoder(&bits, false);
//! assert_eq!(dec16.collect::<Vec<_>>(), vec![4,7, 86]);
//! ```
//! # Performance
//! Regular Fibonacci encoding is up to speed with other rust implementations, e.g. [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate (which I took some code from):
//! - this crate: 75ms/ 1M integers 
//! - fibonnaci_codec: 88ms / 1M integers
//! 
//! Regular fibonacci decoding (iterator based) is up to speed with the [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate. 
//! - regular decoding: 92ms/ 1M integers
//! - fibonnaci_codec: 108ms / 1M integers
//! 
//! The **FastFibonacci** decoding functions are ~2x faster, but have some constant overhead (i.e. only pays of when decoding *many* integers):
//! - fast decoding (u8 segments): 40ms / 1M integers
//! - fast decoding (u16 segments): 30ms / 1M integers
//! - fast decoding (using an iterator): 54ms / 1M integers
//! 
pub mod fibonacci;
mod utils;
mod fastutils;
pub mod fast;
use bitvec::prelude as bv;

/// The type of bitvector used in the crate.
/// Importantly, some code *relies* on `Msb0`
pub(crate) type MyBitSlice = bv::BitSlice<u8, bv::Msb0>;
/// reftype that goes with [`MyBitSlice`]
pub(crate) type MyBitVector = bv::BitVec<u8, bv::Msb0>;


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