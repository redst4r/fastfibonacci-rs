//! Fibonacci-decodes a single `u16` via a lookup table
use std::collections::VecDeque;
use std::io::Read;
use crate::byte_decode::partial::Partial;
use super::partial::number_plus_partial;
use super::{bytestream_transform::U64BytesToU16, faster::{LookupTableNew, LookupVecNew}};


/// decodes as many numbers from the buffer as possible, returning the fully decoded numbers
/// and the partially decoded result
/// 
/// Basically a single lookup in the table, plus some integration with the previous partial result
/// 
/// modifies `decoded_numbers` (overwrites whatever is in it) and `partial`
pub fn decode_all_u16(buf: u16, partial: &mut Partial, table:&LookupVecNew<u16>, decoded_numbers: &mut Vec<u64>) /*-> (Vec<u64>, Partial) */{
	// let mut decoded_numbers = Vec::new();
	decoded_numbers.clear();

	let (numbers, new_partial) = table.lookup(crate::fastutils::State(partial.last_bit == 1), buf);

	// the logic to integrate the old partial and new partial
	// now, we need to properly decode those numbers:
	// if the previous segment left over something (see partial)
	// we need to "add" this to numbers[0]
	// if not, we need to merge p (the new partial decode from stream[i]) and partial (the old partial decode from stream(i-1))

	// this line does two things: 
	// 1. if we got some returned numbers, we split it into numbers[0], numbers[1..] and 
	//    update the first number with its prev partial decoding
	// 2. if no new numbers (->None), just updated the partial
	match numbers.split_first() {
		Some((first, tail)) => {
			// println!("Combining {numbers:?} with {partial:?}");
			// absorb `partial` (the old decoding) into the number
			// and keep the new decoding status as is
			let new_x = number_plus_partial(*first, partial);
			decoded_numbers.push(new_x);
			decoded_numbers.extend(tail);
			*partial = new_partial.to_owned();
		}
		None => {
			// "add" p and partial; ORDER is important
			let mut newp = new_partial.clone();
			newp.combine_partial(partial);
			*partial = newp.to_owned();
		}
	}
}


#[cfg(test)]
mod testing {
	use crate::{byte_decode::byte_manipulation::bits_to_fibonacci_generic_array_u64, utils::create_bitvector};
	use super::*;

	#[test]
	fn test_decode_all_from_partial(){

		// decoding two number and theremaineder
		let bits = create_bitvector(vec![ 
			0,0,1,1,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  
		]).to_bitvec();
		let encoded_bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let u = U64BytesToU16::new(encoded_bytes.as_slice()).collect::<Vec<_>>()[0];

        let table = LookupVecNew::new();
		// println!("u: {u}");

		let mut numbers = Vec::with_capacity(10);
		let mut pa = Default::default();
		decode_all_u16(u, &mut pa, &table, &mut numbers);
		// let mut dd = U16Fast { buf: u, table: &table};
		// let (numbers, pa) = dd.decode_all_from_partial(&Default::default());
		assert_eq!(pa,  Partial::new(0, 2, 0));
		assert_eq!(numbers, vec![3,55]);


		// no decoding, just remaineder
		let bits = create_bitvector(vec![ 
			0,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
		]).to_bitvec();
		let encoded_bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let u = U64BytesToU16::new(encoded_bytes.as_slice()).collect::<Vec<_>>()[0];

		let mut numbers = Vec::with_capacity(10);
		let mut pa = Default::default();
		decode_all_u16(u, &mut pa, &table, &mut numbers);
		// let mut dd = U16Fast { buf: u, table: &table};
		// let (numbers, pa) = dd.decode_all_from_partial(&Default::default());
		assert_eq!(pa,  Partial::new(2, 16, 0));
		assert_eq!(numbers, vec![]);

    }
}

/// Fibonacci decoder running on a byte stream. Collects u64s from the bytestream
/// and decodes them
pub struct U16DecoderFast < 'a, R:Read> {
	u64stream: U64BytesToU16<R>,  /// a stream of u64s
	partial: Partial,
	n_u16s_consumed: usize, // keep track of how many u64 we consumed
	emission_buffer: VecDeque<u64>,
	table: &'a LookupVecNew<u16>,
}

impl <'a, R:Read> U16DecoderFast<'a, R> {
	/// creates a new decoder for the `stream` using the given lookup table
	pub fn new(stream: R, table: &'a LookupVecNew<u16>) ->Self {

		let mut it = U64BytesToU16::new(stream);

		// a bit odd, we need to fill int the first decoding manually
		let el = it.next().unwrap();

		let mut numbers = Vec::with_capacity(10);
		let mut partial = Default::default();
		decode_all_u16(el, &mut partial, &table, &mut numbers);

		let emission_buffer: VecDeque<_> = numbers.into();
		U16DecoderFast {
			u64stream: it, 
			partial, 
			n_u16s_consumed: 1,
			emission_buffer,
			table
		}
	}

	/// get the original byte-stream.
	/// 
	/// If there's any unfinished decoding, this will throw an error
	/// (making sure every single bit has been processed).
	/// Basically we must be at the end of the current u64 (or there's only 0 left)
	/// and dec_status is empty too
	// pub fn get_inner(self) -> Result<R, Partial>  {

	// 	if self.is_clean() {
	// 		Ok(self.u64stream. into_inner())
	// 	} else {
	// 		panic!("unprocessed bits left {:?}", self.partial);
	// 		// return Err(DecodeError::PartiallyDecoded(self.dec_status))
	// 	}
	// }

	/// checks whether the current status of the decoder is clean,
	/// i.e. there's no Partial decoding and the rest of the current u64
	/// is all zero-bits
	pub fn is_clean(&self) -> bool {
		self.partial.is_clean() // TODO this doesnt check if the remaining u16 is all zero??!
	}

	/// returns how many u64s have been pulled from the stream (ie. 8x this is the number of bytes consumed)
	pub fn get_consumed_u16s(&self) -> usize {
		self.n_u16s_consumed
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
			match self.u64stream.next() {
				// managed to pull in another u64
				Some(el) => {

					// decode the entire u16
					let mut numbers = Vec::with_capacity(10);
					decode_all_u16(el, &mut self.partial, self.table, &mut numbers);
					self.emission_buffer = numbers.into();
					self.n_u16s_consumed += 1;
				},
				// we ran out of u64s! 
				None => {
					// if the partial decoding is just zeros; thats the padding which can be ignored/
					// If we see this, we're truely done with decoding
					if self.partial.is_clean() {
						return None
					} else {
						panic!("ran out of u16s to decode, but still have incomplete decoding {:?}", self.partial);
					}
				}				
			}		
		}

		// now we have something in the emission buffer
		let el = self.emission_buffer.pop_front().expect("emission_buffer must have an element");
		Some(el)
	}
}


#[cfg(test)]
mod testing2 {
	use super::*;
    use crate::{byte_decode::byte_manipulation::bits_to_fibonacci_generic_array_u64, utils::create_bitvector};

	#[test]
	fn test_simple(){
		let bits = create_bitvector(vec![ 
			0,0,1,1,0,0,0,0, //7
			0,0,0,0,1,1,0,0, //8  the u64 ends here!
			1,1,0,0,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			]).to_bitvec();
		let bytes = bits_to_fibonacci_generic_array_u64(&bits);
		
		println!("{:?}", bytes);
		let table = LookupVecNew::new();
		let mut dd = U16DecoderFast::new(bytes.as_slice(), &table);
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
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
		// encoded=swap_endian(&encoded, 8);

		let table = LookupVecNew::new();
		let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
		assert_eq!(
			dd.next(),
			Some(4052739537881)
		);
		// let x = dd.get_inner().unwrap();
		// assert_eq!(x, vec![192,0,0,0,0,0,0,0])
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
		// let x = dd.get_inner().unwrap();
		// assert_eq!(x, vec![192, 0,0,0,0,0,0,0])
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


	/// TODO currently, not get_inner possible
	// #[test]
	// #[should_panic(expected = "unprocessed bits left")]
	// fn tset_get_inner_fail(){
	// 	let bits = create_bitvector(vec![ 
	// 		0,0,0,0,0,0,0,0, //1 
	// 		0,0,0,0,0,0,0,0, //2
	// 		0,0,0,0,0,0,0,0, //3
	// 		0,0,0,0,0,0,0,0, //4
	// 		0,0,0,0,0,0,0,0, //5
	// 		0,0,0,0,0,0,0,0, //6
	// 		0,0,0,0,0,0,0,0, //7
	// 		0,0,0,0,1,1,0,1, //8  the u64 ends here!
	// 		1,1,0,0,0,0,0,0, //1 
	// 		0,0,0,0,0,0,0,0, //2
	// 		0,0,0,0,0,0,0,0, //3
	// 		0,0,0,0,0,0,0,0, //4
	// 		0,0,0,0,0,0,0,0, //5
	// 		0,0,0,0,0,0,0,0, //6
	// 		0,0,0,0,0,0,0,0, //7
	// 		0,0,0,0,0,0,0,0, //8  the u64 ends here!
	// 		]).to_bitvec();
	// 	let encoded = bits_to_fibonacci_generic_array(&bits);
	// 	// encoded=swap_endian(&encoded, 8);
	// 	let table = LookupVecNew::new();

	// 	let mut dd = U16DecoderFast::new(encoded.as_slice(), &table);
	// 	assert_eq!(
	// 		dd.next(),
	// 		Some(4052739537881)
	// 	);
	// 	// let x = dd.get_inner().unwrap();
	// 	// assert_eq!(x, vec![0,0,0,0,0,0,0, 192])
	// }


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
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
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
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
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
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
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
		let encoded = bits_to_fibonacci_generic_array_u64(&bits);
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