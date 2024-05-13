//!

// #[test]
// fn testing_stuff(){
// 	let bytes = vec![
// 		0_u8,1,2,3,4,5,6,7,
// 		8   ,9,1,2,3,4,5,6,
// 		8   ,9,1,2,3,4,5,6,
// 		8   ,9,1,2,3,4,5,6,
// 		0, 0, 0, 0, 0, 0, 0, 0];

// 	let v = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    
// 	let chunks: Vec<Vec<i32>> = v.chunks(3).map(|c| c.to_vec()).collect();

// 	let fh = File::open("/tmp/test.txt").unwrap();
// 	let r = BufReader::new(fh);


// 	for b in r.bytes()..chunks(8).map(|chunk| chunk.collect()){
// 		let c: Vec<_> = b.collect();
// 		let x = u64::from_be_bytes(c.try_into().unwrap());
// 		println!("{}", x);
// 	}
// }

// use bitvec::field::BitField;
// use funty::Integral;

use crate::byte_decode::byte_manipulation::read_bit_u64;
use crate::utils::FIB64;
use crate::byte_decode::partial::Partial;

/// Nicer version of `decode_single_dirty_64` using a struct
pub struct Dirty32 <'a> {
	///
	pub buf: &'a [u32], 
	///
	pub buf_size: usize, 
	///
	pub bitpos: usize, 
	///
	pub bufpos: usize, 
	// num: u64, 
	// i_fibo: usize,
}
impl <'a> Dirty32 <'a> {

	/// decode a new number from the stream
	pub fn decode(&mut self) -> Result<u64, Partial> {
		self.decode_from_partial(0, 0, 0)
	}

	/// Decoding, starting from a previous partial decoding
	pub fn decode_from_partial(&mut self, mut num: u64, mut i_fibo: usize, mut last_bit: u64) -> Result<u64, Partial>{
		const WORDSIZE:usize = std::mem::size_of::<u32>() * 8; //sizeof(T) * 8;

		let mut bit = read_bit_u32(self.buf[self.bufpos], self.bitpos) as u64;
		// let mut last_bit = 0;

		self.bitpos = (self.bitpos + 1) % WORDSIZE; // this is inly fast if WORDSIZE  is a power of 2, = 2^n ; however this IS the case
		if self.bitpos == 0 {
			self.bufpos += 1;
		}

		while last_bit + bit < 2 && self.bufpos < self.buf_size {
			num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
			i_fibo += 1;
			last_bit = bit;
			bit = read_bit_u32(self.buf[self.bufpos], self.bitpos) as u64;

			self.bitpos = (self.bitpos +1) % WORDSIZE;

			if self.bitpos == 0 {
				self.bufpos += 1;
			}

			// TODO this should not be needed; covered by the loop cond and the after loop code
			if self.bufpos >= self.buf_size {
				return Err(Partial { 
					num: num + bit * FIB64[i_fibo], // beed to increment, accounting for the 
					i_fibo: i_fibo + 1, 
					last_bit: bit 
				})
			}
		}

		if last_bit + bit < 2 {
			Err(Partial { 
				num: num + bit* FIB64[i_fibo], 
				i_fibo: i_fibo + 1, 
				last_bit: bit  
			})
		} else {
			Ok(num)
		}
	}
}


/// Nicer version of `decode_single_dirty_64` using a struct
pub struct Dirty64 <'a> {
	///
	pub buf: &'a [u64], 
	///
	pub buf_size: usize, 
	///
	pub bitpos: usize, 
	///
	pub bufpos: usize, 
	// num: u64, 
	// i_fibo: usize,
}
impl <'a> Dirty64 <'a> {

	/// decode a new number from the stream
	pub fn decode(&mut self) -> Result<u64, Partial> {
		self.decode_from_partial(0, 0, 0)
	}

	/// Decoding, starting from a previous partial decoding
	pub fn decode_from_partial(&mut self, mut num: u64, mut i_fibo: usize, mut last_bit: u64) -> Result<u64, Partial>{
		const WORDSIZE:usize = std::mem::size_of::<u64>() * 8; //sizeof(T) * 8;

		let mut bit = read_bit_u64(self.buf[self.bufpos], self.bitpos) as u64;
		// let mut last_bit = 0;

		self.bitpos = (self.bitpos + 1) % WORDSIZE; // this is inly fast if WORDSIZE  is a power of 2, = 2^n ; however this IS the case
		if self.bitpos == 0 {
			self.bufpos += 1;
		}

		while last_bit + bit < 2 && self.bufpos < self.buf_size {
			num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
			i_fibo += 1;
			last_bit = bit;
			bit = read_bit_u64(self.buf[self.bufpos], self.bitpos) as u64;

			self.bitpos = (self.bitpos +1) % WORDSIZE;

			if self.bitpos == 0 {
				self.bufpos += 1;
			}

			// TODO this should not be needed; covered by the loop cond and the after loop code
			if self.bufpos >= self.buf_size {
				return Err(Partial { 
					num: num + bit * FIB64[i_fibo], // beed to increment, accounting for the 
					i_fibo: i_fibo + 1, 
					last_bit: bit 
				})
			}
		}

		if last_bit + bit < 2 {
			Err(Partial { 
				num: num + bit* FIB64[i_fibo], 
				i_fibo: i_fibo + 1, 
				last_bit: bit
			})
		} else {
			Ok(num)
		}
	}
}

#[cfg(test)]
mod test {
    use crate::{byte_decode::{bare_metal_64::Dirty64, byte_manipulation::bits_to_fibonacci_generic_array}, utils::{create_bitvector, random_fibonacci_stream}};
	use super::*;

	#[test]
	fn test_correctness_dirty64(){
		use crate::bit_decode::fibonacci::FibonacciDecoder;
		let n = 1_000_000;
		// let N = 1000;
		let data_encoded = random_fibonacci_stream(n, 1, 10000, 123);
		let encoded_bytes = bits_to_fibonacci_generic_array::<u64>(&data_encoded);

		let mut decoded = Vec::with_capacity(n);
		let bitpos = 0;
		let bufpos = 0;

		let mut dd: Dirty64<'_> = Dirty64 { buf: &encoded_bytes, buf_size: encoded_bytes.len(), bitpos, bufpos};
		for _i in 0..n {
			// println!("number: {_i}");
			match dd.decode() {
				Ok(n) => {
					decoded.push(n);
				},
				Err(e) => {
					println!("{:?}", e);
					println!("{n}");
					assert_eq!(1,0);
				},
			}
		}

		// ground thruth
		let dec = FibonacciDecoder::new(&data_encoded, false);
		let decoded_truth: Vec<_> = dec.collect();
		
		assert_eq!(decoded_truth, decoded);
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
		let bitpos = 0;
		let bufpos = 0;

		let mut dd = Dirty64 { buf: &encoded, buf_size: encoded.len(), bitpos, bufpos};
		assert_eq!(
			dd.decode(),
			Ok(4052739537881)
		);

		assert_eq!(
			dd.decode(),
			Err(Partial {num: 0, i_fibo:2 , last_bit: 0})
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
		let bitpos = 0;
		let bufpos = 0;

		let mut dd: Dirty64<'_> = Dirty64 { buf: &encoded, buf_size: encoded.len(), bitpos, bufpos};
		assert_eq!(
			dd.decode(),
			Ok(4052739537881)
		);

		assert_eq!(
			dd.decode(),
			Err(Partial {num: 2, i_fibo:2 , last_bit: 1})
		);

		let bits = create_bitvector(vec![
			1,0,1,1,0,0,0,0, //1 
			0,0,0,0,0,0,0,0, //2
			0,0,0,0,0,0,0,0, //3
			0,0,0,0,0,0,0,0, //4
			0,0,0,0,0,0,0,0, //5
			0,0,0,0,0,0,0,0, //6
			0,0,0,0,0,0,0,0, //7
			0,0,0,0,0,0,0,0, //8  the u64 ends here! this needs to return a PartialDecode num=2, i_fibo=2, lastbit = 1
			])
		.to_bitvec();
		let encoded = bits_to_fibonacci_generic_array::<u64>(&bits);
		let mut dd = Dirty64 { buf: &encoded, buf_size: encoded.len(), bitpos:0, bufpos:0};
		assert_eq!(
			dd.decode_from_partial(2, 2, 1),
			Ok(2)
		);

	}
}

///
#[inline]
pub fn read_bit_u32(x: u32, pos: usize) -> bool {
	// assert!(pos < 32);
	const WORDSIZE:usize = std::mem::size_of::<u32>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}

