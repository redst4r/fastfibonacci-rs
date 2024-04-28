//! 
//! 
use std::io::Read;
use bitvec::field::BitField;
use crate::MyBitSlice;
use crate::fibonacci::encode;


fn read_bit(x: u8, pos: usize, wordsize: usize) -> bool {
	let thebit = x >> (wordsize - 1 - pos) & 1;
	thebit>0
}

fn read_bit_u64(x: u64, pos: usize, wordsize: usize) -> bool {
	let thebit = x >> (wordsize - 1 - pos) & 1;
	thebit>0
}

#[derive(Debug)]
///
pub enum MyErrorType {
    /// 
    Truncated(Vec<u8>),
}

fn u8vec_to_u64vec(u8vec: Vec<u8>) -> Vec<u64>{

	assert_eq!(u8vec.len() % 8, 0);
	let n_elements = u8vec.len() / 8; // elemts for the real (u64) buffer
	let factor = 8; // 8 u8 elements per u64 element

	let mut target = Vec::with_capacity(n_elements);
	for seg in u8vec.chunks(factor) {
		let u: [u8; 8] =seg.try_into().unwrap();
		let x = u64::from_ne_bytes(u);
		target.push(x);
	}
	target
}


#[inline]
/// reads u64 from the stream into the given buffer. Might not fill the entire buffer!!
/// # Returns
/// - Ok(n): the number of u64 elements read: i.e. buffer[0..n] are filled
fn load_into_u64buffer(stream: &mut impl Read, buffer: &mut[u64]) -> Result<usize, MyErrorType>{

	// trying to fill a buffer of u64 with max N elements
	let mut bsize = 0; // keep track of the actual number of elements we were able to fill

	const WORDSIZE: usize = std::mem::size_of::<u64>();
	let mut tbuffer = [0_u8; WORDSIZE];

	// try to read one element into each buffer position
	while bsize < buffer.len() {
		match stream.read(&mut tbuffer) {
			Ok(WORDSIZE) => {
				println!("8 bytes");
				// got 8 bytes, turn into u64 and add to buffer
				let el = u64::from_ne_bytes(tbuffer);
				buffer[bsize] = el;
				bsize += 1;
			},
			Ok(n) => {
				println!("{n} bytes");
				// got less than 8 bytes
				// we should probably return those bytes, in case we need them
				return Err(MyErrorType::Truncated(tbuffer[..n].to_vec()));
			}
			Err(_) => todo!(),
		}
	};
	Ok(bsize)
}

#[derive(Debug)]
///
pub enum MyErrorType3 {
    /// 
    TruncatedU64,
}

use crate::utils::bitstream_to_string;

///
pub fn int_to_fibonacci_bytes(the_ints: &[u64])  -> Vec<u8>{
	let b = encode(the_ints);
	dbg!(&b);
	bits_to_fibonacci_bytes(b.as_bitslice())
}
