//! Repeatedly reads 8bytes into a u64 and 
//! decodes those using the [`Dirty64Single`].
//! 
use std::io::Read;
use crate::byte_decode::partial::Partial;
use super::chunker::U64BytesToU64;

/// Fibonacci decoder running on a byte stream. Collects u64s from the bytestream
/// and decodes them
pub struct U64Decoder <R:Read> {
	u64stream: U64BytesToU64<R>,  /// a stream of u64s
	decoder: Dirty64Single, /// each u64 gets loaded into here for decoding
	dec_status: Partial,
	n_u64s_consumed: usize // keep track of how many u64 we consumed
}

impl <R:Read> U64Decoder<R> {
	///
	pub fn new(stream: R) ->Self {
		let mut it = U64BytesToU64::new(stream);
		let el = it.next().unwrap();
		// println!("El loaded {}", el);
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
			Some(el) => {
				// println!("\tLoading new u64");
				self.decoder = Dirty64Single::new(el); // TODO lots of allocations
				self.dec_status = partial; // carry over the current decoding status
				self.n_u64s_consumed += 1;
				Ok(())
			},
			// we ran out of u64s! 
			None => {
				// println!("\tRan out of u64, dec: {:?}", partial);
				// if the partial decoding is just zeros; thats the padding which can be ignored/
				// If we see this, we're truely done with decoding
				if partial.is_clean() {
					Err("End of Decoding".to_string())
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
    use crate::byte_decode::byte_manipulation::bits_to_fibonacci_generic_array;
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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);

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
		let encoded = bits_to_fibonacci_generic_array(&bits);
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


use crate::utils::FIB64;
use super::byte_manipulation::read_bit_u64;

const WORDSIZE_IN_BITS:usize = std::mem::size_of::<u64>() * 8; //sizeof(T) * 8;

///
#[derive(Debug)]
pub struct Dirty64Single {
	/// the current bits to decode, stored as a u64
	buf: u64, 
	/// which bit (of the 64) we have to decode next
	bitpos: usize, 
}
impl Dirty64Single {
	///
	pub fn new(buf: u64) -> Self {
		Self {buf, bitpos: 0}
	}

	/// decode a new number from the stream
	pub fn decode(&mut self) -> Result<u64, Partial> {
		let fresh_dec = Default::default();
		self.decode_from_partial(fresh_dec)
	}

	/// Decoding, starting from a previous partial decoding
	/// pretty ugly function, seems to be slighty faster than `decode_from_partial2`
	/// so i'll keep it around for now
	pub fn decode_from_partial2(&mut self, partial: Partial) -> Result<u64, Partial>{
 
		let mut num = partial.num;
		let mut i_fibo = partial.i_fibo;
		let mut last_bit = partial.last_bit;

		if self.bitpos > 63 {
			println!("{:?}", self);
			println!("num {}, ifibo {} lastbit {}", num, i_fibo, last_bit);
			panic!("overflow!!")
		}
		let mut bit = read_bit_u64(self.buf, self.bitpos) as u64;

		self.bitpos += 1;
		if self.bitpos >= WORDSIZE_IN_BITS {
            if last_bit + bit < 2 {
                return Err(Partial::new( 
                    num + bit* FIB64[i_fibo], 
                     i_fibo + 1, 
                     bit 
				))
            } else {
                return Ok(num)
            }
		}

		while last_bit + bit < 2 {
			num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
			i_fibo += 1;
			last_bit = bit;
			bit = read_bit_u64(self.buf, self.bitpos) as u64;

			self.bitpos += 1;

			if self.bitpos >= WORDSIZE_IN_BITS {
                if last_bit + bit < 2 {
                    return Err(Partial::new( 
                        num + bit* FIB64[i_fibo], 
                        i_fibo + 1, 
                        bit  
					))
                } else {
                    return Ok(num)
                }	
            }
		}

		if last_bit + bit < 2 {
			Err(Partial::new( 
				num + bit* FIB64[i_fibo], 
				i_fibo + 1, 
				bit  
			))
		} else {
			Ok(num)
		}
	}

	/// just a nicer version of decode_from_partial (moved the bitreading logic into `Partial`)
	pub fn decode_from_partial(&mut self, mut partial: Partial) -> Result<u64, Partial>{
 
		if self.bitpos > 63 {
			println!("{:?}", self);
			println!("{:?}", partial);
			panic!("overflow!!")
		}

		while self.bitpos < WORDSIZE_IN_BITS {
			let bit = read_bit_u64(self.buf, self.bitpos) as u64;
			self.bitpos += 1;
			// println!("{bit}");
			match partial.update(bit) {
				crate::byte_decode::partial::DecResult::Incomplete => {  /*println!("{:?}", partial) */},
				crate::byte_decode::partial::DecResult::Complete(n) => {
					return Ok(n)
				},
			};
		}
		Err(partial)
	}

	/// checks if all trailing bits (including bits[self.bitpos]) are zero
	/// Returns true also when all bits have been read, i.e. bitpos==64
	pub fn all_trailing_zeros(&self) -> bool {
		for p in self.bitpos..WORDSIZE_IN_BITS {
			if read_bit_u64(self.buf, p) {
				return false
			}
		}
		true
	}

	/// returns true if every bit has been decoded (i.e. the pointer moved past the last bit)
	pub fn is_finished(&self) -> bool {
		self.bitpos >= WORDSIZE_IN_BITS
	}

	/// decodes as many numbers from the buffer as possible, returning the fully decoded numbers
	/// and the partially decoded result
	/// 
	/// Basically loops, rtying to decode a number until we hit a partial decoding
	pub fn decode_all_from_partial(&mut self, partial: Partial) -> (Vec<u64>, Partial) {
		let mut fully_decoded = Vec::new();
		let mut last_partial = partial;

		loop {
			// println!("number: {_i}");
			match self.decode_from_partial(last_partial) {
				Ok(n) => {
					fully_decoded.push(n);
					last_partial = Default::default();
				},
				Err(p) => {
					last_partial = p;
					break;
				},
			}
			if self.is_finished() {
				break
			}
		}

		(fully_decoded,last_partial )
	}
}

#[cfg(test)]
mod testing_dirty_single {
	use crate::{byte_decode::{byte_manipulation::{bits_to_fibonacci_generic_array, load_u64_from_bytes}, chunker::U64BytesToU64}, utils::{create_bitvector}};
	use super::*;

	#[test]
	fn test_fixed_(){
		// this corresponds to a single entry [7]
		// 01011000_000...
		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,0,88]); 
		let mut dd = Dirty64Single { buf, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![7]);
		assert!(pa.is_clean());

		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,0,152]); 
		let mut dd = Dirty64Single { buf, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![6]);
		assert!(pa.is_clean());

		// [6,6]:  [0, 0, 0, 0, 0, 0, 192, 90] (u64: 6539226658941960192)
		let buf = load_u64_from_bytes(&vec![0,0,0,0,0,0,192,90]); 
		let mut dd = Dirty64Single { buf, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![7,7 ]);
		assert!(pa.is_clean());
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
		let bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
		
		let mut dd = Dirty64Single { buf: encoded_u64s[0], bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3, 53316291173]);
		assert_eq!(pa,  Partial::new(5, 4, 1))
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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();


		let mut dd = Dirty64Single { buf: encoded_u64s[0], bitpos:0};
		assert_eq!(dd.all_trailing_zeros(), false);
		let _ = dd.decode();
		assert_eq!(dd.all_trailing_zeros(), true);

		// make sure to return zero even if read every single bit!
		let dd = Dirty64Single { buf: encoded_u64s[0], bitpos:64};
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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();


		let mut dd = Dirty64Single { buf: encoded_u64s[0], bitpos:0};
		assert_eq!(
			dd.decode(),
			Ok(4052739537881)
		);

		assert_eq!(
			dd.decode(),
			Err(Partial::new(0, 2 , 0))
		);

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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();

		let mut dd = Dirty64Single { buf: encoded_u64s[0],  bitpos: 0};
		assert_eq!(
			dd.decode(),
			Ok(4052739537881)
		);

		assert_eq!(
			dd.decode(),
			Err(Partial::new(2,2,1))
		);

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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();

		let mut dd = Dirty64Single { buf: encoded_u64s[0], bitpos:0};

		assert_eq!(
			dd.decode_from_partial(Partial::new(2, 2, 1)),
			Ok(2)
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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();

		let mut d = Dirty64Single {buf: encoded_u64s[0], bitpos: 0};
		assert_eq!(
			d.decode_from_partial(Default::default()),
			Ok(2)
		);
		assert_eq!(d.bitpos, 3);

		assert_eq!(
			d.decode_from_partial(Default::default()),
			Ok(3)
		);
		assert_eq!(d.bitpos, 7);

		assert_eq!(
			d.decode_from_partial(Default::default()),
			Ok(53316291173)
		);
		assert_eq!(d.bitpos, 60);

		assert_eq!(
			d.decode_from_partial(Default::default()),
			Err(Partial::new(5, 4, 1))
		);
		assert_eq!(d.bitpos, 64);

	}

	#[test]
	fn test_decode_from_partial2() {
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
		let encoded_bytes = bits_to_fibonacci_generic_array(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();

		let mut d = Dirty64Single {buf:encoded_u64s[0], bitpos: 0};
		assert_eq!(
			d.decode_from_partial2(Default::default()),
			Ok(2)
		);
		assert_eq!(d.bitpos, 3);

		assert_eq!(
			d.decode_from_partial2(Default::default()),
			Ok(3)
		);
		assert_eq!(d.bitpos, 7);

		assert_eq!(
			d.decode_from_partial2(Default::default()),
			Ok(53316291173)
		);
		assert_eq!(d.bitpos, 60);

		assert_eq!(
			d.decode_from_partial2(Default::default()),
			Err(Partial::new(5, 4, 1))
		);
		assert_eq!(d.bitpos, 64);
	}

	/// ensuring that `decode_from_partial` and `decode_from_partial2` do the same thing.
	/// randlomly create a u64 and decode both ways
	#[test]
	fn test_partial2_randomly() {
		for _ in 0..10_000{
			let mut x: u64 = rand::random();
			if x > FIB64[FIB64.len()-1] {
				x = FIB64[FIB64.len()-1];
			}
			let mut d1 = Dirty64Single {buf:x, bitpos: 0};
			let mut d2 = Dirty64Single {buf:x, bitpos: 0};

			loop {
				let r1 = d1.decode_from_partial(Default::default());
				let r2 = d2.decode_from_partial2(Default::default());

				match (r1, r2) {
						(Ok(n), Ok(m)) => {assert_eq!(n,m)}, // same value decoded
						(Ok(_), Err(_)) => {assert_eq!(1,0)},
						(Err(_), Ok(_)) => {assert_eq!(1,0)},
						(Err(partde), Err(partial)) => {
							assert_eq!(partde.num, partial.num);
							assert_eq!(partde.i_fibo, partial.i_fibo);
							assert_eq!(partde.last_bit, partial.last_bit);
							break;
						},
					}
			}

		}

	}
}

