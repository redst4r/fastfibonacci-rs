//! Byte oriented decoding:
//! Oppposed to [`crate::bit_decode`] this assumes that the input stream comes in bigger chunks (u8/u16/u32/u64)
//! rather than single bits and takes advantage (speed) of this fact.
//! 
//! One drawback: We assume that the block of fibonacci encoding fits neatly into (u8/u16/u32/u64) and we dont need access
//! to any possible trailing bits (containing some other data to be decoded differently).
//! 
// pub mod bare_metal;
pub mod bare_metal_64;
pub mod bare_metal_64single;
pub mod bare_metal_generic_single;
mod chunker;
pub mod partial;
pub mod u64_fibdecoder;
pub mod faster;