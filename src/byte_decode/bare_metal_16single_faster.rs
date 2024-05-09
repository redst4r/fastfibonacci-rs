//!
use std::collections::VecDeque;
use std::io::Read;
use crate::byte_decode::partial::Partial;
use super::chunker::Chunks;
use super::faster::{number_plus_partial, LookupTableNew, LookupVecNew};

/// Decoding chunks of 16bits using the lookup table
#[derive(Debug)]
pub struct U16Fast<'a> {
	/// the current bits to decode, stored as a u64
	buf: u16, 
	/// which bit (of the 64) we have to decode next
	// bitpos: usize, 
    table: &'a LookupVecNew<u16>,
}
impl <'a> U16Fast <'a> {
	///
	pub fn new(buf: u16, table: &'a LookupVecNew<u16>) -> Self {
		Self {buf, table }
	}

	/// decodes as many numbers from the buffer as possible, returning the fully decoded numbers
	/// and the partially decoded result
	/// 
	/// Basically a single lookup in the table, plus some integration with the previous partial result
	pub fn decode_all_from_partial(&mut self, partial: &Partial) -> (Vec<u64>, Partial) {
		let mut decoded_numbers = Vec::new();

        let (numbers, new_partial) = self.table.lookup(crate::fastutils::State(partial.last_bit as usize), self.buf);

        // the logic to integrate the old partial and new partial
        // now, we need to properly decode those numbers:
        // if the previous segment left over something (see partial)
        // we need to "add" this to numbers[0]
        // if not, we need to merge p (the new partial decode from stream[i]) and partial (the old partial decode from stream(i-1))
        if !numbers.is_empty() {
            // println!("Combining {numbers:?} with {partial:?}");
            // absorb `partial` (the old decoding) into the number
            // and keep the new decoding status as is
            let new_x = number_plus_partial(numbers[0], partial);
            // println!("newx {new_x}");
            decoded_numbers.push(new_x);

            decoded_numbers.extend(&numbers[1..]);


            // numbers[0] = new_x;
            (decoded_numbers, new_partial.clone() )
        } else {
            // "add" p and partial; ORDER is important
            // partial = combine_partial(partial, p)
            let mut newp = new_partial.clone();
            newp.combine_partial(partial);
            (decoded_numbers, newp )
        }
	}
}

#[cfg(test)]
mod testing {
	use crate::utils::bits_to_fibonacci_generic_array;
	use crate::{bit_decode::fibonacci::FibonacciDecoder, utils::create_bitvector};

	use super::*;

	#[test]
	fn test_decode_all_from_partial(){

		// decoding two number and theremaineder
		let bits = create_bitvector(vec![ 
			0,0,1,1,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  
		]).to_bitvec();
		let u = bits_to_fibonacci_generic_array::<u16>(&bits)[0];
        let table = LookupVecNew::new();
		println!("u: {u}");
		let mut dd = U16Fast { buf: u, table: &table};
		let (numbers, pa) = dd.decode_all_from_partial(&Default::default());
		assert_eq!(pa,  Partial::new(0, 2, 0));
		assert_eq!(numbers, vec![3,55]);

		// no decoding, just remaineder
		let bits = create_bitvector(vec![ 
			0,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
		]).to_bitvec();
		let u = bits_to_fibonacci_generic_array::<u16>(&bits)[0];
		let mut dd = U16Fast { buf: u, table: &table};
		let (numbers, pa) = dd.decode_all_from_partial(&Default::default());
		assert_eq!(pa,  Partial::new(2, 16, 0));
		assert_eq!(numbers, vec![]);

    }

	#[test]
	fn test_correctness_dirty64(){
		use crate::utils::test::random_fibonacci_stream;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000);
		// let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u16>(&data_encoded);
        let table = LookupVecNew::new();

		// println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
            let mut dd = U16Fast { buf: encoded_bytes[_i], table: &table};

			let (numbers, pa) = dd.decode_all_from_partial(&last_partial);
			decoded.extend(numbers);
			last_partial = pa;
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		assert_eq!(decoded_truth, decoded);
	}

}


fn load_u16_from_bytes(bytes: &[u8]) -> u16 {
	// with BE we need to swap the entire stream
	// u64::from_be_bytes(bytes.try_into().unwrap())
	
	// do le instead, i.e. the last byte `bytes[7]` is the first to be processed
	u16::from_be_bytes(bytes.try_into().unwrap())
}

/// Fibonacci decoder running on a byte stream. Collects u64s from the bytestream
/// and decodes them
pub struct U16DecoderFast < 'a, R:Read> {
	u64stream: Chunks<R>,  /// a stream of u64s
	decoder: U16Fast<'a>, /// each u64 gets loaded into here for decoding
	partial: Partial,
	n_u16s_consumed: usize, // keep track of how many u64 we consumed
	emission_buffer: VecDeque<u64>,
}

impl <'a, R:Read> U16DecoderFast<'a, R> {
	///
	pub fn new(stream: R, table: &'a LookupVecNew<u16>) ->Self {

		let mut it = Chunks::new(stream, 2);

		// a bit odd, we need to fill int the first decoding manually
		let bytes = it.next().unwrap().unwrap();
		let el = load_u16_from_bytes(&bytes);
		let mut u64dec = U16Fast::new(el, table);
		let (numbers, partial) = u64dec.decode_all_from_partial(&Default::default());

		let emission_buffer: VecDeque<_> = numbers.into();
		U16DecoderFast {
			u64stream: it, 
			decoder: u64dec, 
			partial, 
			n_u16s_consumed: 1,
			emission_buffer,
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
			panic!("unprocessed bits left {:?}", self.partial);
			// return Err(DecodeError::PartiallyDecoded(self.dec_status))
		}
	}

	/// checks whether the current status of the decoder is clean,
	/// i.e. there's no Partial decoding and the rest of the current u64
	/// is all zero-bits
	pub fn is_clean(&self) -> bool {
		// cant be in the middle of a decoding
		self.partial.is_clean()
	}

	/// returns how many u64s have been pulled from the stream (ie. 8x this is the number of bytes consumed)
	pub fn get_consumed_u16s(&self) -> usize {
		self.n_u16s_consumed
	}

	/// tries to pull in a new u64 number
	/// SHOULD ONLY BE DONE WHEN finished with the current u64 in self.decoder
	/// `partial` lets us carry over the decoding state from the pervious u64
	fn pull_in_next_u16(&mut self) -> Result<(), String> {

		assert!(self.emission_buffer.is_empty(), "emission buffer not empty, yield those first");

		match self.u64stream.next() {
			// managed to pull in another u64
			Some(Ok(bytes16)) => {
				// println!("\tLoading new u16: {bytes16:?}");
				let el =load_u16_from_bytes(&bytes16);
				// self.decoder = U16Fast::new(el); // TODO lots of allocations
				self.decoder.buf = el; // TODO lots of allocations
				// self.partial = partial; // carry over the current decoding status
				self.n_u16s_consumed += 1;
				Ok(())
			},

			// some error in the stream
			Some(Err(e)) => {
				panic!("not sure what happend. io error probably {:?}", e);
			}

			// we ran out of u64s! 
			None => {
				// println!("\tRan out of u16, dec: {:?}", self.partial);
				// if the partial decoding is just zeros; thats the padding which can be ignored/
				// If we see this, we're truely done with decoding
				if self.partial.last_bit == 0 && self.partial.num == 0 {
					Err("End of Decoding".to_string())
				} else {
					panic!("ran out of u16s to decode, but still have incomplete decoding {:?}", self.partial);
				}
			}
		}		
	}
}

impl<'a , R:Read> Iterator for U16DecoderFast<'a, R> {
	type Item = u64;

	fn next(&mut self) -> Option<Self::Item> {

		//Options:
		// 1. we still have some items in emission buffer
		// 2. emission buffer is empty; until we get something into the emission buffer:
		//	 2a. sucess: decode the u16, add decoded numbers to emissions
		//   2b no more u16 avaiable: either return None (if we finsiehd off the decoding) or panic (if theres a remainder)

		while self.emission_buffer.is_empty() {
			// in case the decoder is finished (the last number decoded exaclty flush withthe u64 border)
			// try to pull in a new number
			// println!("try pulling in new number");
			match self.pull_in_next_u16() {
				Ok(()) => { /* nothing, just continue the loop, trying to decode */},
				Err(s) => {
					if s == *"End of Decoding" {
						return None
					}
				},
			}			
			
			// println!("Decoding: buf {},  {:?}", self.decoder.buf, self.partial);
			// decode the current element
			let (decoded_numbers, partial )= self.decoder.decode_all_from_partial(&self.partial);

			self.partial = partial;
			self.emission_buffer.extend(decoded_numbers);
		}

		// now we have something in the emission buffer
		let el = self.emission_buffer.pop_front().expect("emission_buffer must have an element");
		Some(el)
	}
}

// impl<'a> FbDecNew<'a> for U64Decoder<'a> {
// 	fn get_remaining_buffer(&self) -> &'a impl Read {
// 		todo!()
// 	}

// 	fn get_bytes_processed(&self) -> usize {
// 		todo!()
// 	}
// }
#[cfg(test)]
mod testing2 {
	use super::*;
    use crate::utils::{bits_to_fibonacci_generic_array, create_bitvector};
	// pub (crate) fn swap_endian(bytes: &[u8], wordsize: usize) -> Vec<u8>{
	// 	let mut swapped_endian: Vec<u8> = Vec::with_capacity(bytes.len());
	// 	for bytes in bytes.chunks(wordsize){
	// 		swapped_endian.extend(bytes.iter().rev());
	// 	}
	// 	swapped_endian
	// }

	#[test]
	fn test_simple(){
		let bits = create_bitvector(vec![ 
			0,0,1,1,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array(&bits);
		println!("{:?}", encoded);
		let table = LookupVecNew::new();
		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
		assert_eq!(
			dd.next(),
			Some(3)
		);
		assert_eq!(
			dd.next(),
			Some(55)
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
		// encoded=swap_endian(&encoded, 8);

		let table = LookupVecNew::new();
		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		let x = dd.get_inner().unwrap();
		assert_eq!(x, vec![192,0,0,0,0,0,0,0])
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
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();
		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
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
		assert_eq!(x, vec![192, 0,0,0,0,0,0,0])
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
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
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
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		let x = dd.get_inner().unwrap();
		assert_eq!(x, vec![0,0,0,0,0,0,0, 192])
	}


	#[test]
	fn test_dirty64_iter_decode_zero_pad() {
		let bits = create_bitvector(vec![ 
			0,0,1,1,0,0,0,0, //1 
			1,1,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here!
			// this would be fine; the buffer is just zero padded!
			]).to_bitvec();
		let encoded = bits_to_fibonacci_generic_array(&bits);
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(),&table);
		assert_eq!(
			dd.next(),
			Some(3)
		);
		assert_eq!(
			dd.next(),
			Some(8)
		);

		assert_eq!(
			dd.next(),
			None
		);
	}

	#[test]
	#[should_panic(expected = "ran out of u16s to decode, but still have incomplete decoding Partial { num: 1, i_fibo: 2, last_bit: 0 }")]
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
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(),&table);
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
		// encoded=swap_endian(&encoded, 8);
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(),&table);
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
		let table = LookupVecNew::new();

		let mut dd = U16DecoderFast::new(encoded.as_slice(),&table);
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