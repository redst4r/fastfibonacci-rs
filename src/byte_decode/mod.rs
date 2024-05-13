//! Byte oriented decoding:
//! Oppposed to [`crate::bit_decode`] this assumes that the input stream comes in bigger chunks (u8/u16/u32/u64)
//! rather than single bits and takes advantage (speed) of this fact.
//! 
//! One drawback: We assume that the block of fibonacci encoding fits neatly into (u8/u16/u32/u64) and we dont need access
//! to any possible trailing bits (containing some other data to be decoded differently).
//! 

use std::io::Read;
// pub mod bare_metal;
pub mod bare_metal_64;
pub mod bare_metal_64single;
pub mod bare_metal_generic_single;
mod chunker;
pub mod partial;
pub mod u64_fibdecoder;
pub mod faster;
// pub mod generic_fibdecoder;
pub mod bare_metal_16single_faster;
pub mod byte_manipulation;
// pub mod chunker_generic;

/// Marker trait for Fibonacci decoders.
/// This is an iterator over u64 (the decoded integers),
/// allows you to get back the intput iterator once done with decoding
pub trait FbDecNew<'a>: Iterator<Item = u64> {
    /// Returns the buffer behind the last bit processed.
    /// Comes handy when the buffer contains data OTHER than fibonacci encoded
    /// data that needs to be processed externally.
    fn get_remaining_buffer(&self) -> &'a impl Read;

    /// how far did we process into the buffer (pretty much the first bit after a 11).
    fn get_bytes_processed(&self) -> usize;
}