//! Repeatedly reads 8bytes into a u64 and 
//! decodes those using the [`Dirty64Single`].
//! 

use std::io::Read;
use funty::Integral;

use crate::byte_decode::partial::Partial;
use super::bytestream_transform::U64BytesToU64;


/// Takes a single number (`T`: u32/u64) and fibonacci decodes it.
/// As opposed to [`crate::byte_decode::bare_metal_3264_stream`], this
/// decodes only a single number (u32/u64) rather than a stream.
#[derive(Debug)]
pub struct DirtyGenericSingle<T:Integral> {
	/// the current bits to decode, stored as a u32/u64.
	/// The first bit we'll look at is the HIGHEST bit!
	buf: T, 
	/// which bit (of the 32/64) we have to decode next
	bitpos: usize,

	// the status of the decoding; sometimes a call to decode wont yield a complete decoding
	// hence, store it here
	pub (crate) partial: Partial,
}
impl <T:Integral> DirtyGenericSingle<T> {
	/// New Decoder
	pub fn new(buf: T) -> Self {
		Self {buf, bitpos: 0, partial: Default::default()}
	}

	/// adds a new number to decode, carrying over the old decodeing state
	pub fn update_buffer(&mut self, new_buf: T) {
		self.buf = new_buf;
		self.bitpos = 0;
	}

	/// Decodes a single number from the buffer, given a previous unfinished decoding `partial`
	/// just a nicer version of decode_from_partial (moved the bitreading logic into `Partial`)
	pub fn decode_from_partial(&mut self) -> Option<u64>{
 
		if self.bitpos > (T::BITS - 1) as usize {
			println!("{:?}", self);
			println!("{:?}", self.partial);
			panic!("overflow!!")
		}

		while self.bitpos < T::BITS as usize {
			let bit = Self::read_bit(self.buf, self.bitpos) as u64;
			self.bitpos += 1;
			match self.partial.update(bit) {
				crate::byte_decode::partial::DecResult::Incomplete => {  /*println!("{:?}", partial) */},
				crate::byte_decode::partial::DecResult::Complete(n) => {
					// since we decoded a number, reset the partial
					self.partial = Default::default();
					return Some(n)
				},
			};
		}
		None
	}

	/// decodes as many numbers from the buffer as possible, returning the fully decoded numbers
	/// and the partially decoded result
	/// 
	/// Basically loops, rtying to decode a number until we hit a partial decoding
	pub fn decode_all_from_partial(&mut self) -> Vec<u64> {
		let mut fully_decoded = Vec::new();

		while !self.is_finished() {
			match self.decode_from_partial() {
				Some(n) => {
					fully_decoded.push(n);
					self.partial = Default::default();
				},
				None => {
					break;  // tecnhically not needed, after a partial decode, we are always finished
				},
			}
		}
		fully_decoded
	}

	/// checks if all trailing bits (including bits[self.bitpos]) are zero
	/// Returns true also when all bits have been read, i.e. bitpos==64
	pub fn all_trailing_zeros(&self) -> bool {
		for p in self.bitpos..(T::BITS as usize) {
			if Self::read_bit(self.buf, p) {
				return false
			}
		}
		true
	}

	/// returns true if every bit has been decoded (i.e. the pointer moved past the last bit)
	pub fn is_finished(&self) -> bool {
		self.bitpos >= (T::BITS as usize)
	}

	/// 
	pub fn is_clean(&self) -> bool{
		self.is_finished() & self.partial.is_clean()
	 }
    /// reads a single bit at the given position
    #[inline]
    fn read_bit(x: T, pos: usize) -> bool {
        // assert!(pos < 64);
        let shift_op = (T::BITS as usize) - 1 - pos;
        let thebit = (x >> shift_op) & T::ONE;
        thebit > T::ZERO
    }
}


#[cfg(test)]
mod testing {
	use crate::byte_decode::byte_manipulation::testing::load_u64_from_bytes;
	use crate::byte_decode::bytestream_transform::{U64BytesToU16, U64BytesToU8};
	use crate::{byte_decode::byte_manipulation::bits_to_fibonacci_generic_array_u64, utils::create_bitvector};
	use super::*;

	#[test]
	fn test_fixed_(){
		// this corresponds to a single entry [7]
		// 01011000_000...
		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,0,88]); 
		let mut dd = DirtyGenericSingle::new(buf);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![7]);
		assert!(dd.partial.is_clean());

		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,0,152]); 
		let mut dd = DirtyGenericSingle::new(buf);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![6]);
		assert!(dd.partial.is_clean());

		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,192,90]); 
		let mut dd = DirtyGenericSingle::new(buf);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![7,7]);
		assert!(dd.partial.is_clean());
	}

	#[test]
	fn test_decode_all_from_partial(){
		let bits = create_bitvector(vec![ 
			0,1,1,0,0,1,1,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,1,1,0,0,0,1, //8 
			])
		.to_bitvec();
	
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);

		// U64
		let x_u64: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();

		let mut dd = DirtyGenericSingle::new(x_u64[0]);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![2,3, 53316291173]);
		assert_eq!(dd.partial,  Partial::new(5, 4, 1));

		// // U32
		// let x_u32: Vec<u32> = U64BytesToU32::new(bytes.as_slice()).collect();
		// let mut dd = DirtyGenericSingle { buf: x_u32[0], bitpos:0};
		// let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		// assert_eq!(numbers, vec![2,3]);
		// assert_eq!(pa,  Partial::new(0, 25, 0));

		// U16
		let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).collect();
		let mut dd = DirtyGenericSingle::new(x_u16[0]);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![2,3]);
		assert_eq!(dd.partial,  Partial::new(0, 9, 0));


		// U8
		let x_u8: Vec<u8> = U64BytesToU8::new(bytes.as_slice()).collect();

		let mut dd = DirtyGenericSingle::new(x_u8[0]);
		let numbers = dd.decode_all_from_partial();
		assert_eq!(numbers, vec![2,3]);
		assert_eq!(dd.partial,  Partial::new(0, 1, 0));		
	}

	#[test]
	fn test_traliing() {
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here! this needs to return a PartialDecode num=2, i_fibo=2, lastbit = 1
			])
		.to_bitvec();
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
		let mut dd = DirtyGenericSingle::new(encoded[0]);
		assert_eq!(dd.all_trailing_zeros(), false);
		let _ = dd.decode_from_partial();
		assert_eq!(dd.all_trailing_zeros(), true);

		// make sure to return zero even if read every single bit!
		let mut dd = DirtyGenericSingle::new(encoded[0]);
		dd.bitpos = 64;
		assert_eq!(dd.all_trailing_zeros(), true);

	}

	#[test]
	fn test_dirty64overhang2() {
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here! this needs to return a PartialDecode num=2, i_fibo=2, lastbit = 1
			])
		.to_bitvec();
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();

		let mut dd = DirtyGenericSingle::new(encoded[0]);
		assert_eq!(
			dd.decode_from_partial(),
			Some(4052739537881)
		);

		assert_eq!(
			dd.decode_from_partial(),
			None //Err(Partial::new(0, 2 , 0))
		);
		assert_eq!(dd.partial, Partial::new(0, 2 , 0));

	}

	#[test]
	fn test_dirty64overhang() {
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,1, //8  the u64 ends here! this needs to return a PartialDecode num=2, i_fibo=2, lastbit = 1
			])
		.to_bitvec();
	let bytes = bits_to_fibonacci_generic_array_u64(&bits);
	let encoded: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();

		let mut dd = DirtyGenericSingle::new(encoded[0]);
		assert_eq!(
			dd.decode_from_partial(),
			Some(4052739537881)
		);

		assert_eq!(
			dd.decode_from_partial(),
			None // Err(Partial::new(2,2,1))
		);
		assert_eq!(dd.partial, Partial::new(2,2,1));

		let bits = create_bitvector(vec![
			1,0,1,1,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8
			])
		.to_bitvec();
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
		let mut dd = DirtyGenericSingle::new(encoded[0]);
		dd.partial = Partial::new(2, 2, 1);
		assert_eq!(
			dd.decode_from_partial(),
			Some(2)
		);
	}

	#[test]
	fn test_decode_from_partial() {
		let bits = create_bitvector(vec![ 
			0,1,1,0,0,1,1,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,1,1,0,0,0,1, //8 
			])
		.to_bitvec();
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
		let mut d = DirtyGenericSingle::new(encoded[0]);
		assert_eq!(
			d.decode_from_partial(),
			Some(2)
		);
		assert_eq!(d.bitpos, 3);

		d.partial = Default::default();
		assert_eq!(
			d.decode_from_partial(),
			Some(3)
		);
		assert_eq!(d.bitpos, 7);

		d.partial = Default::default();
		assert_eq!(
			d.decode_from_partial(),
			Some(53316291173)
		);
		assert_eq!(d.bitpos, 60);

		d.partial = Default::default();
		assert_eq!(
			d.decode_from_partial(),
			None
		);
		assert_eq!(d.bitpos, 64);
		assert_eq!(d.partial, Partial::new(5, 4, 1));
	}
}


/// Fibonacci decoder running on a byte stream. Collects u64s from the bytestream
/// and decodes them
pub struct U64Decoder <R:Read> {
	u64stream: U64BytesToU64<R>,  /// a stream of u64s
	decoder: DirtyGenericSingle<u64>, /// each u64 gets loaded into here for decoding
	n_u64s_consumed: usize // keep track of how many u64 we consumed
}

impl <R:Read> U64Decoder<R> {
	/// Create a new decoder.
	pub fn new(stream: R) ->Self {
		let mut it = U64BytesToU64::new(stream);
		let el = it.next().unwrap();
		let u64dec = DirtyGenericSingle::new(el);
		U64Decoder {
			u64stream: it, 
			decoder: u64dec, 
			n_u64s_consumed: 1
		}
	}

	/// get the original byte-stream.
	/// 
	/// If there's any unfinished decoding, this will throw an error
	/// (making sure every single bit has been processed).
	/// Basically we must be at the end of the current u64 (or there's only 0 left)
	/// and dec_status is empty too
	pub fn get_inner(self) -> Result<R, Partial>  {

		if self.is_clean() {
			Ok(self.u64stream.into_inner())
		} else {
			panic!("unprocessed bits left {:?}", self.decoder);
			// return Err(DecodeError::PartiallyDecoded(self.dec_status))
		}
	}

	/// checks whether the current status of the decoder is clean,
	/// i.e. there's no Partial decoding and the rest of the current u64
	/// is all zero-bits
	pub fn is_clean(&self) -> bool {
		// cant be in the middle of a decoding
		if !self.decoder.partial.is_clean() {
			false
		} else {
			self.decoder.all_trailing_zeros()
		}
	}

	/// returns how many u64s have been pulled from the stream (ie. 8x this is the number of bytes consumed)
	pub fn get_consumed_u64s(&self) -> usize {
		self.n_u64s_consumed
	}

	/// returns how many u64s have been pulled from the stream (ie. 8x this is the number of bytes consumed)
	pub fn get_consumed_bytes(&self) -> usize {
		self.n_u64s_consumed * 8  // since each u64 has 8 bytes
	}

	/// tries to pull in a new u64 number
	/// SHOULD ONLY BE DONE WHEN finished with the current u64 in self.decoder
	/// `partial` lets us carry over the decoding state from the pervious u64
	fn pull_in_next_u64(&mut self) -> Result<(), String> {

		assert!(self.decoder.is_finished());

		match self.u64stream.next() {
			// managed to pull in another u64
			Some(el) => {
				// println!("\tLoading new u64");
				// self.decoder = DirtyGenericSingle::new(el); // TODO lots of allocations
				self.decoder.update_buffer(el);
				self.n_u64s_consumed += 1;
				Ok(())
			},
			// we ran out of u64s! 
			None => {
				// println!("\tRan out of u64, dec: {:?}", partial);
				// if the partial decoding is just zeros; thats the padding which can be ignored/
				// If we see this, we're truely done with decoding
				if self.is_clean() {
					Err("End of Decoding".to_string())
				} else {
					panic!("ran out of u64s to decode, but still have incomplete decoding {:?}", self.decoder.partial);
				}
			}
		}		
	}
}

impl<R:Read> Iterator for U64Decoder<R> {
	type Item = u64;

	fn next(&mut self) -> Option<Self::Item> {
		// Options
		// 1. we sucessfulled decoded a number (someweher inside the current u64)
		// 2a. we came to the end of the u64 without decoding, but we can load more u64s
		// 2b. we came to the end of the u64, but we're also at the end of the u64 stream
		loop {
			// in case the decoder is finished (the last number decoded exaclty flush withthe u64 border)
			// try to pull in a new number
			if self.decoder.is_finished() {
				// let fresh_partial = Default::default();
				match self.pull_in_next_u64() {
					Ok(()) => { /* nothing, just continue the loop */},
					Err(s) => {
						if s == *"End of Decoding" {
							return None
						}
					},
				}			
			}
			// try decoiding
			match self.decoder.decode_from_partial() {
				Some(n) => {
					// println!("Success {n}");
					// sucessfully decoded a number, initialize clean for the next round
					return Some(n)
				},
				// ran into the end of the current u64
				None => {
					// println!("Partial {:?}", partial);
					match self.pull_in_next_u64() {
						Ok(()) => { /* nothing, just continue the loop */},
						Err(s) => {
							if s == *"End of Decoding" {
								return None
							}
						},
					}
				},
			}
		}
	}
}


#[cfg(test)]
mod testing2 {
    use crate::byte_decode::byte_manipulation::bits_to_fibonacci_generic_array_u64;
    use crate::utils::create_bitvector;
	use crate::byte_decode::u64_fibdecoder::U64Decoder;
	

	#[test]
	fn test_get_inner(){
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		let x = dd.get_inner().unwrap();
		assert_eq!(x, vec![0,0,0,0,0,0,0,192])
	}
	#[test]
	fn tset_get_inner_flush_with_border(){
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,1,1, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		assert_eq!(
			dd.next(),
			Some(1)
		);
		// essentialyl the next u64
		let x = dd.get_inner().unwrap();
		assert_eq!(x, vec![0,0,0,0,0,0,0,192])
	}

	#[test]
	fn tset_get_inner_flush_with_border2(){
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,1,1, //8  the u64 ends here!

			0,0,1,1,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(10610209857723)
		);
		assert_eq!(
			dd.next(),
			Some(3)
		);
		assert_eq!(
			dd.next(),
			None
		)
	}

	#[test]
	#[should_panic(expected = "unprocessed bits left")]
	fn tset_get_inner_fail(){
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,1, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		let x = dd.get_inner().unwrap();
		assert_eq!(x, vec![0,0,0,0,0,0,0, 192])
	}

	#[test]
	fn test_dirty64_iter_decode_zero_pad() {
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!
			// this would be fine; the buffer is just zero padded!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);

		assert_eq!(
			dd.next(),
			None
		);
	}

	#[test]
	#[should_panic(expected = "ran out of u64s to decode, but still have incomplete decoding Partial { num: 1, i_fibo: 2, last_bit: 0 }")]
	fn test_dirty64_iter_leftover_bits() {

		// on the other hand, if there's trailing stuff
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,1,0, //8  the u64 ends here!
			// NOTE THE remaining bit in there
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		assert_eq!(
			dd.next(),
			None
		);
	}

	#[test]
	fn test_dirty64_iter_2u64s() {

		// on the other hand, if there's trailing stuff
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		assert_eq!(
			dd.next(),
			Some(3)
		);
		assert_eq!(
			dd.next(),
			None
		);
	}

	#[test]
	fn test_dirty64_iter_2u64s_2() {

		// on the other hand, if there's trailing stuff
		// here the last bit is NOT set
		let bits = create_bitvector(vec![ 
			0,0,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!

			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
		// encoded=swap_endian(&encoded, 8);

		let mut dd = U64Decoder::new(encoded.as_slice());
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		assert_eq!(
			dd.next(),
			Some(3)
		);
		assert_eq!(
			dd.next(),
			None
		);
	}
}
