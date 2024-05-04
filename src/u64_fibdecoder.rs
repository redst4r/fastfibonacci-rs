//!
//! 
//! 
use std::io::Read;
use crate::{bare_metal_64single::Dirty64Single, chunker::Chunks, partial::Partial};


fn load_u64_from_bytes(bytes: &[u8]) -> u64 {
	// with BE we need to swap the entire stream
	// u64::from_be_bytes(bytes.try_into().unwrap())
	
	// do le instead, i.e. the last byte `bytes[7]` is the first to be processed
	u64::from_le_bytes(bytes.try_into().unwrap())
}

/// Fibonacci decoder running on a byte stream. Collects u64s from the bytestream
/// and decodes them
pub struct U64Decoder <R:Read> {
	u64stream: Chunks<R>,  /// a stream of u64s
	decoder: Dirty64Single, /// each u64 gets loaded into here for decoding
	dec_status: Partial,
	n_u64s_consumed: usize // keep track of how many u64 we consumed
}

impl <R:Read> U64Decoder<R> {
	///
	pub fn new(stream: R) ->Self {

		let mut it = Chunks::new(stream, 8);
		let bytes = it.next().unwrap().unwrap();
		let el = load_u64_from_bytes(&bytes);
		let u64dec = Dirty64Single::new(el);
		U64Decoder {
			u64stream: it, 
			decoder: u64dec, 
			dec_status: Default::default(), 
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
			panic!("unprocessed bits left");
			// return Err(DecodeError::PartiallyDecoded(self.dec_status))
		}
	}

	/// checks whether the current status of the decoder is clean,
	/// i.e. there's no Partial decoding and the rest of the current u64
	/// is all zero-bits
	pub fn is_clean(&self) -> bool {
		// cant be in the middle of a decoding
		let empty_dec = Default::default();
		if self.dec_status !=  empty_dec {
			false
		} else {
			self.decoder.all_trailing_zeros()
		}
	}

	/// returns how many u64s have been pulled from the stream (ie. 8x this is the number of bytes consumed)
	pub fn get_consumed_u64s(&self) -> usize {
		self.n_u64s_consumed
	}

	/// tries to pull in a new u64 number
	/// SHOULD ONLY BE DONE WHEN finished with the current u64 in self.decoder
	/// `partial` lets us carry over the decoding state from the pervious u64
	fn pull_in_next_u64(&mut self, partial: Partial) -> Result<(), String> {

		assert!(self.decoder.is_finished());

		match self.u64stream.next() {
			// managed to pull in another u64
			Some(Ok(bytes8)) => {
				// println!("\tLoading new u64");
				let el =load_u64_from_bytes(&bytes8);
				self.decoder = Dirty64Single::new(el);
				self.dec_status = partial; // carry over the current decoding status
				self.n_u64s_consumed += 1;
				Ok(())
			},

			// some error in the stream
			Some(Err(e)) => {
				panic!("not sure what happend. io error probably {:?}", e);
			}

			// we ran out of u64s! 
			None => {
				println!("\tRan out of u64, dec: {:?}", partial);
				// if the partial decoding is just zeros; thats the padding which can be ignored/
				// If we see this, we're truely done with decoding
				if partial.last_bit == 0 && partial.num == 0 {
					return Err("End of Decoding".to_string());
				} else {
					panic!("ran out of u64s to decode, but still have incomplete decoding {:?}", partial);
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
				let fresh_partial = Default::default();
				match self.pull_in_next_u64(fresh_partial) {
					Ok(()) => { /* nothing, just continue the loop */},
					Err(s) => {
						if s == *"End of Decoding" {
							return None
						}
					},
				}			
			}

			// println!("{:?}", self.dec_status);
			// try decoiding
			match self.decoder.decode_from_partial(self.dec_status.clone()) {
				Ok(n) => {
					// println!("Success {n}");
					// sucessfully decoded a number, initialize clean for the next round
					self.dec_status = Default::default();
					return Some(n)
				},
				// ran into the end of the current u64
				Err(partial) => {
					// println!("Partial {:?}", partial);
					match self.pull_in_next_u64(partial) {
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
mod testing {
    use crate::{utils::bits_to_fibonacci_bytes, u64_fibdecoder::U64Decoder, utils::create_bitvector};
	
	pub (crate) fn swap_endian(bytes: &[u8], wordsize: usize) -> Vec<u8>{
		let mut swapped_endian: Vec<u8> = Vec::with_capacity(bytes.len());
		for bytes in bytes.chunks(wordsize){
			swapped_endian.extend(bytes.iter().rev());
		}
		swapped_endian
	}

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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
		let mut encoded = bits_to_fibonacci_bytes(&bits);
		encoded=swap_endian(&encoded, 8);

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