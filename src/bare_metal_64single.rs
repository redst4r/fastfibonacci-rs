//!
use core::panic;

use crate::{bare_metal_64::{bits_to_fibonacci_u64array, read_bit_u64}, fibonacci::FibonacciDecoder, nobitvec::{DecodeError, PartialDecode}, utils::{bitstream_to_string_pretty, create_bitvector, FIB64}};

const WORDSIZE_IN_BITS:usize = std::mem::size_of::<u64>() * 8; //sizeof(T) * 8;

///
#[derive(Debug)]
pub struct Dirty64Single {
	///
	pub buf: u64, 
	///
	bitpos: usize, 
}
impl Dirty64Single {
	///
	pub fn new(buf: u64) -> Self {
		Self {buf, bitpos: 0}
	}

	/// decode a new number from the stream
	pub fn decode(&mut self) -> Result<u64, DecodeError> {
		self.decode_from_partial(0, 0, 0)
	}

	/// Decoding, starting from a previous partial decoding
	pub fn decode_from_partial(&mut self, mut num: u64, mut i_fibo: usize, mut last_bit: u64) -> Result<u64, DecodeError>{

		if self.bitpos > 63 {
			println!("{:?}", self);
			println!("num {num}, ifibo {i_fibo} lastbit {last_bit}");
			panic!("overflow!!")
		}
		let mut bit = read_bit_u64(self.buf, self.bitpos) as u64;
		// let mut last_bit = 0;

		self.bitpos += 1;
		if self.bitpos >= WORDSIZE_IN_BITS {
            if last_bit + bit < 2 {
                return Err(DecodeError::PartiallyDecoded( PartialDecode { 
                    num: num + bit* FIB64[i_fibo], 
                    i_fibo: i_fibo + 1, 
                    last_bit: bit == 1  
                }))
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
                    return Err(DecodeError::PartiallyDecoded( PartialDecode { 
                        num: num + bit* FIB64[i_fibo], 
                        i_fibo: i_fibo + 1, 
                        last_bit: bit == 1  
                    }))
                } else {
                    return Ok(num)
                }	
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
}

#[test]
fn test_correctness_dirty64(){
    use crate::utils::test::random_fibonacci_stream;
    let n = 1_00000;
    // let N = 1000;
    let data_encoded = random_fibonacci_stream(n, 1, 10000);
	let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);

    // println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
    let mut decoded = Vec::with_capacity(n);

    let mut last_partial = PartialDecode {num:0, i_fibo:0, last_bit: false};
    for _i in 0..encoded_bytes.len() {
	    let mut D = Dirty64Single { 
            buf: encoded_bytes[_i],
            bitpos: 0
        };

        loop {
            // println!("number: {_i}");
            match D.decode_from_partial(last_partial.num, last_partial.i_fibo, last_partial.last_bit as u64) {
                Ok(n) => {
                    decoded.push(n);
                    last_partial = PartialDecode {num: 0, i_fibo:0, last_bit: false}
                },
                Err(DecodeError::PartiallyDecoded(partial)) => {
                    last_partial = partial;
                    break;
                },
		    }
            if D.bitpos >= 64 {
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
	let encoded = bits_to_fibonacci_u64array(&bits);
	let mut dd = Dirty64Single { buf: encoded[0], bitpos:0};
	assert_eq!(dd.all_trailing_zeros(), false);
	let _ = dd.decode();
	assert_eq!(dd.all_trailing_zeros(), true);

	// make sure to return zero even if read every single bit!
	let mut dd = Dirty64Single { buf: encoded[0], bitpos:64};
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
	let encoded = bits_to_fibonacci_u64array(&bits);

	let mut D = Dirty64Single { buf: encoded[0], bitpos:0};
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
	let encoded = bits_to_fibonacci_u64array(&bits);

	let mut D = Dirty64Single { buf: encoded[0],  bitpos: 0};
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
		0,0,0,0,0,0,0,0, //8
		])
	.to_bitvec();
	let encoded = bits_to_fibonacci_u64array(&bits);
	let mut D = Dirty64Single { buf: encoded[0], bitpos:0};
	assert_eq!(
		D.decode_from_partial(2, 2, 1),
		Ok(2)
	);

}


