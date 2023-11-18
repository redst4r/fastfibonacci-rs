pub mod fibonacci;
pub mod fibonacci_fast;
pub mod fibonacci_old;
mod fib_utils;
pub use fib_utils::random_fibonacci_stream;

use bitvec::prelude as bv;

/// The type of bitvector used in the crate.
/// Importantly, some code *relies* on `Msb0`
pub (crate) type MyBitSlice = bv::BitSlice<u8, bv::Msb0>;
/// reftype thqt goes with [`MyBitSlice`]
pub (crate) type MyBitVector = bv::BitVec<u8, bv::Msb0>;
