//!
use crate::byte_decode::partial::Partial;
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
mod testing {
	use crate::{bit_decode::fibonacci::FibonacciDecoder, byte_decode::byte_manipulation::{bits_to_fibonacci_generic_array, load_u64_from_bytes}, utils::{create_bitvector, random_fibonacci_stream}};
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
		let u = bits_to_fibonacci_generic_array::<u64>(&bits)[0];
		let mut dd = Dirty64Single { buf: u, bitpos:0};
		let (numbers, pa) = dd.decode_all_from_partial(Default::default());
		assert_eq!(numbers, vec![2,3, 53316291173]);
		assert_eq!(pa,  Partial::new(5, 4, 1))
	}


	#[test]
	fn test_correctness_dirty64(){
		let n = 1_00000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000, 123);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u64>(&data_encoded);

		// println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
		let mut decoded = Vec::with_capacity(n);

		let mut last_partial = Default::default();
		for _i in 0..encoded_bytes.len() {
			let mut dd = Dirty64Single { 
				buf: encoded_bytes[_i],
				bitpos: 0
			};

			loop {
				// println!("number: {_i}");
				match dd.decode_from_partial(last_partial) {
					Ok(n) => {
						decoded.push(n);
						last_partial = Default::default();
					},
					Err(partial) => {
						last_partial = partial;
						break;
					},
				}
				if dd.bitpos >= 64 {
					break
				}
			}
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
		let mut dd = Dirty64Single { buf: encoded[0], bitpos:0};
		assert_eq!(dd.all_trailing_zeros(), false);
		let _ = dd.decode();
		assert_eq!(dd.all_trailing_zeros(), true);

		// make sure to return zero even if read every single bit!
		let dd = Dirty64Single { buf: encoded[0], bitpos:64};
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

		let mut dd = Dirty64Single { buf: encoded[0], bitpos:0};
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

		let mut dd = Dirty64Single { buf: encoded[0],  bitpos: 0};
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
		let mut dd = Dirty64Single { buf: encoded[0], bitpos:0};

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
		let mut d = Dirty64Single {buf:u, bitpos: 0};
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
		let u = bits_to_fibonacci_generic_array::<u64>(&bits)[0];
		let mut d = Dirty64Single {buf:u, bitpos: 0};
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

