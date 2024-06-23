//! [Fibonacci encoding](https://en.wikipedia.org/wiki/Fibonacci_coding) of integers, 
//! via the 
//! [FastFibonacci encoding](https://ceur-ws.org/Vol-567/paper14.pdf) or 
//! [FastFibonacci decoding](https://www.semanticscholar.org/paper/Fast-data-Encoding-and-Deconding-Algorithms-Walder/4fbae5afc34dd32e7527fe4b1a1bd19e68794e3d) 
//! algorithm.
//! 
//! The whole package works in two alternative ways (see `Bit- vs Bytestreams`):
//! 1. En/Decoding bit-by bit via the [`bitvec`]-crate
//! 2. En/Decoding entire  chunks of bits (represented as u8,u16,u32,u64)
//!
//! ## Introduction: Fibonacci Encoding
//! [Fibonacci encoding](https://en.wikipedia.org/wiki/Fibonacci_coding) is a variable-length encoding of integers, 
//! with the special property that any encoding of an interger ends in `1` (binary) and no encoding contains `11`. 
//! Hence one can use `11` as a separator in a stream of Fibonacci encoded integers.
//! 
//! - *Regular Fibonacci* en/decoding works decoding bit by bit, which can be quite slow. 
//! - [FastFibonacci decoding](https://www.semanticscholar.org/paper/Fast-data-Encoding-and-Deconding-Algorithms-Walder/4fbae5afc34dd32e7527fe4b1a1bd19e68794e3d)
//! looks at `n` bits at once, decoding this chunk in a single operation which can be faster. *Note*: this is distinct from the bit/byte representation (see next section).
//! 
//! ### Bit- vs Bytestreams
//! The crate is divided into two parts: 
//! - `bit_decode` (misnomer, not only for decoding), which represents input as [`bitvec::prelude::BitVec`] 
//! and allows to decode arbitrary sequences of bits. Once we're done with decoding we can retriueve the remaining bistream for further processing
//! - `byte_decode`, which does *not* operate on bits but assumes each block of Fibonacci-encoded numbers comes as a sequence of `u8` (or `u16`, `u32`, `u64`).
//! The stream might contain other data after, but it is assumed that this transition happens at the `u8` (`u16` etc) boundary. This makes it less flexible, but
//! faster than processing bit by bit.
//! 
//! Both approaches support an on the fly decoding and a **fast** decoding (using a lookup table of precomputed partial decodings).
//! 
//! # Examples
//! ## Regular encoding and decoding:
//! ```rust
//! use fastfibonacci::bit_decode::fibonacci::{encode, decode, FibonacciDecoder};
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
//! ## Fast decoding:
//! We'll stick to the bit-decoding version here, analogous approach doing chunks of bits.
//! 
//! 1. Create an object implementing the [`bit_decode::fast::LookupTable`] trait (expensive), 
//!    which decodes multiple bits in a chunk.
//!    The crate provides the following implementations of the trait: 
//!     - [`bit_decode::fast::LookupVec<u8>`]: Decoding 8 bits at a time.
//!     - [`bit_decode::fast::LookupVec<u16>`]: Decoding 16 bits at a time.
//!    
//!     ***NOTE***:  There's also a (lazy) static version of this precomputed table via 
//!     - [`bit_decode::fast::FB_LOOKUP_U8`]
//!     - [`bit_decode::fast::FB_LOOKUP_U16`]
//!     which can be useful if the lookup table is needed in different places (but only calculated once)
//! 2. The lookup table can then be used to do any amount of decoding via a [`bit_decode::fast::FastFibonacciDecoder`].
//!    It's either instantiated 
//!     - explicitly via [`bit_decode::fast::FastFibonacciDecoder::new()`]
//!     - or via the helper functions [`bit_decode::fast::get_u8_decoder`], [`bit_decode::fast::get_u16_decoder`].
//! 
//!    ***Note***: For simplicity, there's also the [`bit_decode::fast::fast_decode`] function, which skips the Decoder and just immediately decodes the sequence.
//! 
//! ```rust
//! use fastfibonacci::bit_decode::fibonacci::encode;
//! use fastfibonacci::bit_decode::fast::{fast_decode,LookupVec, get_u8_decoder, get_u16_decoder};
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
//! ## Regular Encoding/Decoding
//! Regular Fibonacci encoding is up to speed with other rust implementations, e.g. [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate (which I took some code from):
//! - this crate: 75ms/ 1M integers 
//! - fibonnaci_codec: 88ms / 1M integers
//! 
//! Regular fibonacci decoding (iterator based) is up to speed with the [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate. 
//! - regular decoding (bitwise): 92ms/ 1M integers
//! - regular decoding (bytewise): 66ms/ 1M integers
//! - fibonnaci_codec: 108ms / 1M integers

//! ## Fast Encoding/Decoding
//! The **FastFibonacci** decoding functions are ~2x faster, but have some constant overhead (i.e. only pays of when decoding *many* integers):
//! - fast decoding (bitwise, u8 segments): 40ms / 1M integers
//! - fast decoding (bitwise, u16 segments): 30ms / 1M integers
//! - fast decoding (bitwise, using an iterator): 54ms / 1M integers
//! 
//! - fast decoding (bytewise, u8 segments): 24ms / 1M integers
//! - fast decoding (bytewise, u16 segments): 22ms / 1M integers
//! - fast decoding (bytewise, using an iterator): 30ms / 1M integers
//! 
// pub mod fibonacci;
pub mod utils;
mod fastutils;
// pub mod fast;

pub mod byte_decode;
pub mod bit_decode;

// regular bit encoding/decoding
pub use bit_decode::{FbDec, fibonacci::FibonacciDecoder, fibonacci::encode, fibonacci::decode};
// fast bit-decoding
pub use bit_decode::fast::FastFibonacciDecoder;


// regular byte decoding
pub use byte_decode::u64_fibdecoder::U64Decoder;
pub use byte_decode::faster::fast_decode_new;
