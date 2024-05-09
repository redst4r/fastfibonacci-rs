//!
use funty::Integral;
use crate::byte_decode::partial::Partial;

///
#[derive(Debug)]
pub struct DirtyGenericSingle<T:Integral> {
	/// the current bits to decode, stored as a u64
	buf: T, 
	/// which bit (of the 64) we have to decode next
	bitpos: usize, 
}
impl <T:Integral> DirtyGenericSingle<T> {
	///
	pub fn new(buf: T) -> Self {
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
	// pub fn decode_from_partial2(&mut self, partial: Partial) -> Result<u64, Partial>{
 
	// 	let mut num = partial.num;
	// 	let mut i_fibo = partial.i_fibo;
	// 	let mut last_bit = partial.last_bit as u64;

	// 	if self.bitpos > 63 {
	// 		println!("{:?}", self);
	// 		println!("num {}, ifibo {} lastbit {}", num, i_fibo, last_bit);
	// 		panic!("overflow!!")
	// 	}
	// 	let mut bit = read_bit_u64(self.buf, self.bitpos) as u64;

	// 	self.bitpos += 1;
	// 	if self.bitpos >= WORDSIZE_IN_BITS {
    //         if last_bit + bit < 2 {
    //             return Err(Partial::new( 
    //                 num + bit* FIB64[i_fibo], 
    //                  i_fibo + 1, 
    //                  bit 
	// 			))
    //         } else {
    //             return Ok(num)
    //         }
	// 	}

	// 	while last_bit + bit < 2 {
	// 		num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
	// 		i_fibo += 1;
	// 		last_bit = bit;
	// 		bit = read_bit_u64(self.buf, self.bitpos) as u64;

	// 		self.bitpos += 1;

	// 		if self.bitpos >= WORDSIZE_IN_BITS {
    //             if last_bit + bit < 2 {
    //                 return Err(Partial::new( 
    //                     num + bit* FIB64[i_fibo], 
    //                     i_fibo + 1, 
    //                     bit  
	// 				))
    //             } else {
    //                 return Ok(num)
    //             }	
    //         }
	// 	}

	// 	if last_bit + bit < 2 {
	// 		Err(Partial::new( 
	// 			num + bit* FIB64[i_fibo], 
	// 			i_fibo + 1, 
	// 			bit  
	// 		))
	// 	} else {
	// 		Ok(num)
	// 	}
	// }

	/// Decodes a single number from the buffer, given a previous unfinished decoding `partial`
	/// just a nicer version of decode_from_partial (moved the bitreading logic into `Partial`)
	pub fn decode_from_partial(&mut self, mut partial: Partial) -> Result<u64, Partial>{
 
		if self.bitpos > (T::BITS - 1) as usize {
			println!("{:?}", self);
			println!("{:?}", partial);
			panic!("overflow!!")
		}

		while self.bitpos < T::BITS as usize {
			let bit = Self::read_bit(self.buf, self.bitpos) as u64;
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

	/// decodes as many numbers from the buffer as possible, returning the fully decoded numbers
	/// and the partially decoded result
	/// 
	/// Basically loops, rtying to decode a number until we hit a partial decoding
	pub fn decode_all_from_partial(&mut self, partial: Partial) -> (Vec<u64>, Partial) {
		let mut fully_decoded = Vec::new();
		let mut last_partial = partial;

		while !self.is_finished() {
			// println!("number: {_i}");
			match self.decode_from_partial(last_partial) {
				Ok(n) => {
					fully_decoded.push(n);
					last_partial = Default::default();
				},
				Err(p) => {
					last_partial = p;
					break;  // tecnhically not needed, after a partial decode, we are always finished
				},
			}
		}

		(fully_decoded,last_partial )
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
    #[inline]
    pub fn read_bit(x: T, pos: usize) -> bool {
        // assert!(pos < 64);
        let shift_op = (T::BITS as usize) - 1 - pos;
        let thebit = (x >> shift_op) & T::ONE;
        thebit > T::ZERO
    }
}


#[cfg(test)]
mod testing {
	use crate::utils::bits_to_fibonacci_generic_array;
	use crate::{bit_decode::fibonacci::FibonacciDecoder, utils::create_bitvector};

	use super::*;

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

		// U64
		let u = bits_to_fibonacci_generic_array::<u64>(&bits)[0];

		let mut dd = DirtyGenericSingle { buf: u, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3, 53316291173]);
		assert_eq!(pa,  Partial::new(5, 4, 1));

		// U32
		let u = bits_to_fibonacci_generic_array::<u32>(&bits)[0];
		let mut dd = DirtyGenericSingle { buf: u, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3]);
		assert_eq!(pa,  Partial::new(0, 25, 0));

		// U16
		let u = bits_to_fibonacci_generic_array::<u16>(&bits)[0];
		let mut dd = DirtyGenericSingle { buf: u, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3]);
		assert_eq!(pa,  Partial::new(0, 9, 0));


		// U8
		let u = bits_to_fibonacci_generic_array::<u8>(&bits)[0];
		let mut dd = DirtyGenericSingle { buf: u, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3]);
		assert_eq!(pa,  Partial::new(0, 1, 0));		
	}

	#[test]
	fn test_correctness_dirty64(){
		use crate::utils::test::random_fibonacci_stream;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000);
		// let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u64>(&data_encoded);
        
		// println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
			let mut dd = DirtyGenericSingle { 
				buf: encoded_bytes[_i],
				bitpos: 0
			};

			let (numbers, pa) = dd.decode_all_from_partial(last_partial);
			decoded.extend(numbers);
			last_partial = pa;
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		assert_eq!(decoded_truth, decoded);
	}

	#[test]
	fn test_correctness_dirty32(){
		use crate::utils::test::random_fibonacci_stream;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000);
		// let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u32>(&data_encoded);
        
		// println!("{}", bitstream_to_string_pretty(&data_encoded, 32));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
			let mut dd = DirtyGenericSingle { 
				buf: encoded_bytes[_i],
				bitpos: 0
			};

			let (numbers, pa) = dd.decode_all_from_partial(last_partial);
			decoded.extend(numbers);
			last_partial = pa;
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		assert_eq!(decoded_truth, decoded);
	}	

	#[test]
	fn test_correctness_dirty16(){
		use crate::utils::test::random_fibonacci_stream;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000);
		// let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u16>(&data_encoded);
        
		// println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
			let mut dd = DirtyGenericSingle { 
				buf: encoded_bytes[_i],
				bitpos: 0
			};

			let (numbers, pa) = dd.decode_all_from_partial(last_partial);
			decoded.extend(numbers);
			last_partial = pa;
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		assert_eq!(decoded_truth, decoded);
	}

	#[test]
	fn test_correctness_dirty8(){
		use crate::utils::test::random_fibonacci_stream;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000);
		// let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u8>(&data_encoded);
        
		// println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
			let mut dd = DirtyGenericSingle { 
				buf: encoded_bytes[_i],
				bitpos: 0
			};

			let (numbers, pa) = dd.decode_all_from_partial(last_partial);
			decoded.extend(numbers);
			last_partial = pa;
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		assert_eq!(decoded_truth, decoded);
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
		let encoded = bits_to_fibonacci_generic_array::<u64>(&bits);
		let mut dd = DirtyGenericSingle { buf: encoded[0], bitpos:0};
		assert_eq!(dd.all_trailing_zeros(), false);
		let _ = dd.decode();
		assert_eq!(dd.all_trailing_zeros(), true);

		// make sure to return zero even if read every single bit!
		let dd = DirtyGenericSingle { buf: encoded[0], bitpos:64};
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
		let encoded = bits_to_fibonacci_generic_array::<u64>(&bits);

		let mut dd = DirtyGenericSingle { buf: encoded[0], bitpos:0};
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
		let encoded = bits_to_fibonacci_generic_array::<u64>(&bits);

		let mut dd = DirtyGenericSingle { buf: encoded[0],  bitpos: 0};
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
		let encoded = bits_to_fibonacci_generic_array::<u64>(&bits);
		let mut dd = DirtyGenericSingle { buf: encoded[0], bitpos:0};

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
		let u = bits_to_fibonacci_generic_array::<u64>(&bits)[0];
		let mut d = DirtyGenericSingle {buf:u, bitpos: 0};
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

	// #[test]
	// fn test_decode_from_partial2() {
	// 	let bits = create_bitvector(vec![ 
	// 		0,1,1,0,0,1,1,0, //1 
	// 		0,0,0,0,0,0,0,0, //2
	// 		0,0,0,0,0,0,0,0, //3
	// 		0,0,0,0,0,0,0,0, //4
	// 		0,0,0,0,0,0,0,0, //5
	// 		0,0,0,0,0,0,0,0, //6
	// 		0,0,0,0,0,0,0,0, //7
	// 		0,0,1,1,0,0,0,1, //8 
	// 		])
	// 	.to_bitvec();
	// 	let u = bits_to_fibonacci_u64array(&bits)[0];
	// 	let mut d = DirtyGenericSingle {buf:u, bitpos: 0};
	// 	assert_eq!(
	// 		d.decode_from_partial2(Default::default()),
	// 		Ok(2)
	// 	);
	// 	assert_eq!(d.bitpos, 3);

	// 	assert_eq!(
	// 		d.decode_from_partial2(Default::default()),
	// 		Ok(3)
	// 	);
	// 	assert_eq!(d.bitpos, 7);

	// 	assert_eq!(
	// 		d.decode_from_partial2(Default::default()),
	// 		Ok(53316291173)
	// 	);
	// 	assert_eq!(d.bitpos, 60);

	// 	assert_eq!(
	// 		d.decode_from_partial2(Default::default()),
	// 		Err(Partial::new(5, 4, 1))
	// 	);
	// 	assert_eq!(d.bitpos, 64);
	// }

	// /// ensuring that `decode_from_partial` and `decode_from_partial2` do the same thing.
	// /// randlomly create a u64 and decode both ways
	// #[test]
	// fn test_partial2_randomly() {
	// 	for _ in 0..10_000{
	// 		let mut x: u64 = rand::random();
	// 		if x > FIB64[FIB64.len()-1] {
	// 			x = FIB64[FIB64.len()-1];
	// 		}
	// 		let mut d1 = DirtyGenericSingle {buf:x, bitpos: 0};
	// 		let mut d2 = DirtyGenericSingle {buf:x, bitpos: 0};

	// 		loop {
	// 			let r1 = d1.decode_from_partial(Default::default());
	// 			let r2 = d2.decode_from_partial2(Default::default());

	// 			match (r1, r2) {
	// 					(Ok(n), Ok(m)) => {assert_eq!(n,m)}, // same value decoded
	// 					(Ok(_), Err(_)) => {assert_eq!(1,0)},
	// 					(Err(_), Ok(_)) => {assert_eq!(1,0)},
	// 					(Err(partde), Err(partial)) => {
	// 						assert_eq!(partde.num, partial.num);
	// 						assert_eq!(partde.i_fibo, partial.i_fibo);
	// 						assert_eq!(partde.last_bit, partial.last_bit);
	// 						break;
	// 					},
	// 				}
	// 		}

	// 	}

	// }
}

