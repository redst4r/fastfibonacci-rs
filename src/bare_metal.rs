//! 
//! 
//! 
//! 
use crate::fibonacci::FibonacciDecoder;
use crate::nobitvec::{bits_to_fibonacci_bytes, int_to_fibonacci_bytes, DecodeError, PartialDecode};
use crate::utils::{bitstream_to_string, bitstream_to_string_pretty, create_bitvector};
// use std::io::{self, BufRead, BufReader};
// use std::io::{Error, Read};
// use std::ops::{Add, Shr, Sub, BitAnd};
// use bitvec::slice::BitSlice;
// use bitvec::vec::BitVec;
use bitvec::{bits, bitvec, field::BitField, order::{Lsb0, Msb0}};
use crate::{fibonacci::encode, utils::FIB64};

/// see https://togglebit.io/posts/rust-bitwise/
/// However, this reads the bits from the left side
/// i.e. pos=0 will read out the Most significant bit!
#[inline]
fn read_bit(x: u8, pos: usize) -> bool {
	// assert!(pos < 8);
	const WORDSIZE:usize = std::mem::size_of::<u8>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}

#[test]
fn test_read_bit() {
	assert_eq!(read_bit(0b0000_0000, 0), false, "0 pos 0");
	assert_eq!(read_bit(0b0000_0000, 1), false, "0 pos 1");
	assert_eq!(read_bit(0b1000_0000, 0), true, "2 pos 0");
	assert_eq!(read_bit(0b1000_0000, 1), false, "2 pos 1");
	assert_eq!(read_bit(0b0100_0000, 0), false, "2 pos 1");
	assert_eq!(read_bit(0b0100_0000, 1), true, "2 pos 1");
}

///
pub fn decode_single_dirty(buf: &[u8], buf_size: usize, bitpos: &mut usize, bufpos: &mut usize, num: &mut u64, i_fibo: &mut usize) -> Result<(), DecodeError> {

	const WORDSIZE:usize = std::mem::size_of::<u8>() * 8; //sizeof(T) * 8;
	let buf_offset = *bufpos;
	let bit_offset = WORDSIZE - *bitpos % WORDSIZE -1;

	let mut bit = read_bit(buf[*bufpos], *bitpos) as u64;
	let mut last_bit = 0;

	*bitpos = (*bitpos + 1) % WORDSIZE;
	if *bitpos == 0 {
		*bufpos += 1;
	}

	while last_bit + bit < 2 && *bufpos < buf_size {
		*num += bit * FIB64[*i_fibo];
		*i_fibo += 1;
		last_bit = bit;
		bit = read_bit(buf[*bufpos], *bitpos) as u64;

		*bitpos = (*bitpos +1) % WORDSIZE;

		if *bitpos == 0 {
			*bufpos += 1;
		}

		if *bufpos >= buf_size {
			return Err(DecodeError::PartiallyDecoded( PartialDecode { num: *num, i_fibo: *i_fibo + 1, last_bit: bit == 1 }))
		}
	}

	if last_bit + bit < 2 {
		Err(DecodeError::PartiallyDecoded( PartialDecode { num: *num, i_fibo: *i_fibo + 1, last_bit: bit == 1  }))
	} else {
		Ok(())
	}
}

/// deconding a single (maybe paritalled decoded ) number from the bytes
// pub fn decode_single_dirty3(buf: &[u8], buf_size: usize, bitpos: &mut usize, bufpos: &mut usize, num: &mut u64, i_fibo: &mut usize) -> Result<(), DecodeError> {

// 	const DEBUG: bool = false;
//     // bits per unit
// 	const SIZE:usize = std::mem::size_of::<u8>() * 8; //sizeof(T) * 8;
// 	// assert!(*bufpos < buf_size);
// 	// assert!(*bitpos < SIZE);

// 	let mut last_bit = 0;

// 	let mut bit = read_bit(buf[*bufpos], *bitpos) as u64;

// 	if DEBUG{
// 		println!("INSIDE:\n---------------\ncurrent bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo} BIT {bit}");
// 		println!("---------------\n");
// 	}
// 	// *bufpos = *bufpos + (*bitpos + 1) / SIZE;
// 	// *bitpos = (*bitpos + 1) % SIZE;

// 	*bitpos = *bitpos + 1;

// 	if *bitpos==SIZE {
// 		*bufpos += 1;
// 		*bitpos = 0;
// 	}
// 	if *bufpos >= buf_size {
// 		return Err(DecodeError::PartiallyDecoded( PartialDecode { num: *num, i_fibo: *i_fibo + 1, last_bit: bit == 1  }))
// 	}


// 	while last_bit + bit < 2 && *bufpos < buf_size
// 	{
// 		last_bit = bit;
// 		*num += bit * FIB64[*i_fibo];

// 		if *bitpos==SIZE {
// 			*bufpos += 1;
// 			*bitpos = 0;
// 		}
// 		// *bufpos = *bufpos + (*bitpos + 1) / SIZE;
// 		// *bitpos = dbg!((dbg!(*bitpos) + 1) % SIZE);

// 		if *bufpos >= buf_size {
// 			return Err(DecodeError::PartiallyDecoded( PartialDecode { num: *num, i_fibo: *i_fibo + 1, last_bit: bit == 1  }))
// 		}
		
// 		bit = read_bit(buf[*bufpos], *bitpos) as u64;
// 		if DEBUG{
// 			println!("LOOP:\n---------------\ncurrent bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo} BIT {bit}");
// 			println!("---------------\n");
// 		}
// 		// *bitpos+=1;
// 		*bitpos = *bitpos + 1;
// 		*i_fibo+=1;
// 	}

// 	assert_eq!(last_bit + bit, 2);
// 	assert!(*bufpos <= buf_size);

// 	*bufpos = *bufpos + *bitpos / SIZE;
// 	*bitpos = *bitpos % SIZE;

// 	Ok(())
// }

#[test]
fn test_decode_dirty() {
	let bits = create_bitvector(vec![ 
		0,0,0,0,0,0,1,1, //1 :: 21
		1,1,0,0,0,0,1,0, //2 :: 1, 8
		// 0,0,0,0,0,0,1,1, //3
		// 0,0,0,0,0,0,0,0, //4
		// 0,0,0,0,0,0,0,0, //5
		// 0,0,0,0,0,0,0,0, //6
		// 0,0,0,0,0,0,0,0, //7
		// 1,1,0,0,0,0,1,1, //8
		// 0,0,0,0,0,0,1,0, //9
		])
	.to_bitvec();
	let encoded = bits_to_fibonacci_bytes(&bits);

	let buf_size = encoded.len();
	let mut bitpos = 0;
	let mut bufpos = 0;

	let mut num = 0 ;
	let mut i_fibo = 0;
	assert_eq!(
		decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo),
		Ok(())
	);
	assert_eq!(num, 21);

	num = 0; // need to reset
	i_fibo = 0;	
	assert_eq!(
		decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo),
		Ok(())
	);
	assert_eq!(num, 1);

	num = 0; // need to reset
	i_fibo = 0;
	let  r = decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo);
	assert_eq!(
		r, 
		Err(DecodeError::PartiallyDecoded(PartialDecode { num: 8, i_fibo: 6, last_bit: false })));

}

#[test]
fn test_decode_dirty_debug() {
	let bits = create_bitvector(vec![
		0,0,0,0,0,0,1,1, //1 :: 21
		1,1,0,0,0,0,1,0, //2 :: 1, 8
		// 0,0,0,0,0,0,1,1, //3
		// 0,0,0,0,0,0,0,0, //4
		// 0,0,0,0,0,0,0,0, //5
		// 0,0,0,0,0,0,0,0, //6
		// 0,0,0,0,0,0,0,0, //7
		// 1,1,0,0,0,0,1,1, //8
		// 0,0,0,0,0,0,1,0, //9
		])
	.to_bitvec();
	let encoded = bits_to_fibonacci_bytes(&bits);
    println!("{}", bitstream_to_string(&bits));

	println!("Len)encoded){}",encoded.len());
	let buf_size = encoded.len();
	let mut bitpos = 0;
	let mut bufpos = 0;
	let mut num = 0 ;
	let mut i_fibo = 0;

	decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
	println!("num {num}\n");
	// println!("bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo}\n");

	num = 0; // need to reset
	i_fibo = 0;
	decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
	println!("num {num}\n");
	// println!("bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo}\n");

	num = 0; // need to reset
	i_fibo = 0;
	let  r = decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo);
	assert_eq!(
		r, 
		Err(DecodeError::PartiallyDecoded(PartialDecode { num: 8, i_fibo: 6, last_bit: false})));

	// complete the decoding

	let bits = create_bitvector(vec![
		// 0,0,0,0,0,0,1,1, //1 :: 21
		// 1,1,0,0,0,0,1,0, //2 :: 1, 8
		0,1,1,0,0,0,1,1, //3
		])
	.to_bitvec();
	let encoded = bits_to_fibonacci_bytes(bits.as_bitslice());
	let buf_size = encoded.len();
	// let num = r.err().unwrap();
	let mut num=8;
	let mut i_fibo = 6;
	let mut bufpos = 0;
	let mut bitpos = 0;

	decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();

	assert_eq!(num, 8+34)
	// println!("bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo}\n");


	// num = 0; // need to reset
	// i_fibo = 0;
	// decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo);
	// println!("num {num}\n");
	// // println!("bitpos {bitpos}\nbufpos {bufpos}\nnum {num}\niFibo {i_fibo}\n");

	// num = 0; // need to reset
	// i_fibo = 0;
	// decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo);
	// println!("num {num}\n");

	// num = 0; // need to reset
	// i_fibo = 0;
	// decode_single_dirty(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo);
	// println!("num {num}\n");
}


#[test]
fn test_correctness(){
    use crate::utils::test::random_fibonacci_stream;
    let N = 100_000;
    let data_encoded = random_fibonacci_stream(N, 1, 10000);
	let encoded_bytes = bits_to_fibonacci_bytes(&data_encoded);
    println!("{}", bitstream_to_string_pretty(&data_encoded, 8));

    // 10111011|0110011x
    // let x = vec![3,4,2,3];
    // let N = x.len();
	// let encoded_bytes = dbg!(int_to_fibonacci_bytes(&x));
    // let data_encoded = encode(&x);
    // println!("len encoded_bytes{}", encoded_bytes.len());
    // println!("{}", bitstream_to_string_pretty(&data_encoded, 8));


    let mut decoded = Vec::with_capacity(N);

    let mut bitpos = 0;
    let mut bufpos = 0;
    let mut num = 0;
    let mut i_fibo = 0;

    for _i in 0..N {
        // println!("number: {_i}");
        match decode_single_dirty(
			&encoded_bytes, 
			encoded_bytes.len(), 
			&mut bitpos, 
			&mut bufpos, 
			&mut num, 
			&mut i_fibo
		) {
			Ok(()) => {/* */},
			Err(e) => {
				println!("{:?}", e);
				println!("{N}");
				assert_eq!(1,0);
			},
		}
		decoded.push(num);

        // reset
        num = 0;
        i_fibo = 0;
		// println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    }

    // ground thruth
    let dec = FibonacciDecoder::new(&data_encoded, false);
    let decoded_truth: Vec<_> = dec.collect();
    
    assert_eq!(decoded_truth, decoded);
}



/// Nicer version of `decode_single_dirty_64` using a struct
pub struct Dirty8 <'a> {
	///
	pub buf: &'a [u8], 
	///
	pub buf_size: usize, 
	///
	pub bitpos: usize, 
	///
	pub bufpos: usize, 
	// num: u64, 
	// i_fibo: usize,
}
impl <'a> Dirty8 <'a> {

	/// decode a new number from the stream
	pub fn decode(&mut self) -> Result<u64, DecodeError> {
		self.decode_from_partial(0, 0, 0)
	}

	/// Decoding, starting from a previous partial decoding
	pub fn decode_from_partial(&mut self, mut num: u64, mut i_fibo: usize, mut last_bit: u64) -> Result<u64, DecodeError>{
		const WORDSIZE:usize = std::mem::size_of::<u8>() * 8; //sizeof(T) * 8;

		let mut bit = read_bit(self.buf[self.bufpos], self.bitpos) as u64;
		// let mut last_bit = 0;

		self.bitpos = (self.bitpos + 1) % WORDSIZE;
		if self.bitpos == 0 {
			self.bufpos += 1;
		}

		while last_bit + bit < 2 && self.bufpos < self.buf_size {
			num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
			i_fibo += 1;
			last_bit = bit;
			bit = read_bit(self.buf[self.bufpos], self.bitpos) as u64;

			self.bitpos = (self.bitpos +1) % WORDSIZE;

			if self.bitpos == 0 {
				self.bufpos += 1;
			}

			// TODO this should not be needed; covered by the loop cond and the after loop code
			if self.bufpos >= self.buf_size {
				return Err(DecodeError::PartiallyDecoded( PartialDecode { 
					num: num + bit * FIB64[i_fibo], // beed to increment, accounting for the 
					i_fibo: i_fibo + 1, 
					last_bit: bit == 1  
				}))
			}
		}

		if last_bit + bit < 2 {
			Err(DecodeError::PartiallyDecoded( PartialDecode { 
				num: num + bit* FIB64[i_fibo], 
				i_fibo: i_fibo + 1, 
				last_bit: bit == 1  
			}))
		} else {
			Ok(num)
		}
	}
}

#[test]
fn test_correctness_dirty8(){
    use crate::utils::test::random_fibonacci_stream;
    let n = 1_000_000;
    // let N = 1000;
    let data_encoded = random_fibonacci_stream(n, 1, 10000);
	let encoded_bytes = bits_to_fibonacci_bytes(&data_encoded);

    let mut decoded = Vec::with_capacity(n);
    let bitpos = 0;
    let bufpos = 0;

	let mut D = Dirty8 { buf: &encoded_bytes, buf_size: encoded_bytes.len(), bitpos, bufpos};
    for _i in 0..n {
        // println!("number: {_i}");
        match D.decode() {
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
fn test_dirty8overhang2() {
	// here the last bit is NOT set
	let bits = create_bitvector(vec![
		0,0,0,0,0,0,0,0, //1 
		0,0,0,0,0,0,0,0, //2
		0,0,0,0,0,0,0,0, //3
		0,0,0,0,0,0,0,0, //4
		0,0,0,0,0,0,0,0, //5
		0,0,0,0,0,0,0,0, //6
		0,0,0,0,0,0,0,0, //7
		0,0,0,0,1,1,0,0, //8  the u64 ends here! this needs to return a PartialDecode num=0, i_fibo=2, lastbit = 1
		])
	.to_bitvec();
	let encoded = bits_to_fibonacci_bytes(&bits);
    let bitpos = 0;
    let bufpos = 0;

	let mut D = Dirty8 { buf: &encoded, buf_size: encoded.len(), bitpos, bufpos};
	assert_eq!(
		D.decode(),
		Ok(4052739537881)
	);

	assert_eq!(
		D.decode(),
		Err(DecodeError::PartiallyDecoded(PartialDecode {num: 0, i_fibo:2 , last_bit: false}))
	);

}

#[test]
fn test_dirty8overhang() {
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
	let encoded = bits_to_fibonacci_bytes(&bits);
    let bitpos = 0;
    let bufpos = 0;

	let mut D = Dirty8 { buf: &encoded, buf_size: encoded.len(), bitpos, bufpos};
	assert_eq!(
		D.decode(),
		Ok(4052739537881)
	);

	assert_eq!(
		D.decode(),
		Err(DecodeError::PartiallyDecoded(PartialDecode {num: 2, i_fibo:2 , last_bit: true}))
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
	let encoded = bits_to_fibonacci_bytes(&bits);
	let mut D = Dirty8 { buf: &encoded, buf_size: encoded.len(), bitpos:0, bufpos:0};
	assert_eq!(
		D.decode_from_partial(2, 2, 1),
		Ok(2)
	);
}
