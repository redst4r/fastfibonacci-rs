//! Contains Dirty32 and Dirty64, which both take a stream of u32/u64 and fibonacci-decode those numbers bit by bit

use crate::byte_decode::byte_manipulation::{read_bit_u32, read_bit_u64};
use crate::utils::FIB64;
use crate::byte_decode::partial::Partial;

/// Fib-Decode a single u32 
pub struct Dirty32 <'a> {
	/// the buffer of u32s to decode
	pub buf: &'a [u32], 
	///  len of buf
	pub buf_size: usize, 
	/// next bit in buf[bupos] to pull
	pub bitpos: usize, 
	/// position in buffer to decode next
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
	/// the buffer storing the values to be decoded
	pub buf: &'a [u64], 
	/// length of self.buf
	pub buf_size: usize, 
	/// which bit to read in self.buf[self.bufpos]
	pub bitpos: usize, 
	/// Position in self.buf (points to the next element to be process)
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
    use crate::{byte_decode::{byte_manipulation::bits_to_fibonacci_generic_array_u64, bytestream_transform::U64BytesToU64}, utils::create_bitvector};
	use super::*;

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
		let encoded_bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();


		let bitpos = 0;
		let bufpos = 0;

		let mut dd = Dirty64 { buf: &encoded_u64s, buf_size: encoded_u64s.len(), bitpos, bufpos};
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
		let encoded_bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();


		let bitpos = 0;
		let bufpos = 0;

		let mut dd: Dirty64<'_> = Dirty64 { buf: &encoded_u64s, buf_size: encoded_u64s.len(), bitpos, bufpos};
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
		let encoded_bytes = bits_to_fibonacci_generic_array_u64(&bits);
		let encoded_u64s: Vec<u64> = U64BytesToU64::new(encoded_bytes.as_slice()).collect();

		let mut dd = Dirty64 { buf: &encoded_u64s, buf_size: encoded_u64s.len(), bitpos:0, bufpos:0};
		assert_eq!(
			dd.decode_from_partial(2, 2, 1),
			Ok(2)
		);

	}
}


