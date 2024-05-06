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

use bitvec::field::BitField;
use funty::Integral;

use crate::{fibonacci::FibonacciDecoder, partial::Partial, utils::{create_bitvector, FIB64}, MyBitSlice};

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

#[test]
fn test_correctness_dirty64(){
    use crate::utils::test::random_fibonacci_stream;
    let n = 1_000_000;
    // let N = 1000;
    let data_encoded = random_fibonacci_stream(n, 1, 10000);
	let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);

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
	let encoded = bits_to_fibonacci_u64array(&bits);
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
	let encoded = bits_to_fibonacci_u64array(&bits);
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
	let encoded = bits_to_fibonacci_u64array(&bits);
	let mut dd = Dirty64 { buf: &encoded, buf_size: encoded.len(), bitpos:0, bufpos:0};
	assert_eq!(
		dd.decode_from_partial(2, 2, 1),
		Ok(2)
	);

}


/// see https://togglebit.io/posts/rust-bitwise/
/// However, this reads the bits from the left side
/// i.e. pos=0 will read out the Most significant bit!
#[inline]
pub fn read_bit_u64(x: u64, pos: usize) -> bool {
	// assert!(pos < 64);
	const WORDSIZE:usize = std::mem::size_of::<u64>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
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

#[test]
fn test_read_bit() {
	assert_eq!(read_bit_u64(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), false, "0 pos 0");
	assert_eq!(read_bit_u64(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), false, "0 pos 1");
	assert_eq!(read_bit_u64(0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), true, "2 pos 0");
	assert_eq!(read_bit_u64(0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), false, "2 pos 1");
	assert_eq!(read_bit_u64(0b01000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), false, "2 pos 1");
	assert_eq!(read_bit_u64(0b01000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), true, "2 pos 1");
}

/// turns a bitstream into chunks of u64
/// Note: the last byte will be right-padded if the encoding doesnt fill the netire byte
pub fn bits_to_fibonacci_u64array(b: &MyBitSlice) -> Vec<u64>{

    const WORDSIZE: usize = std::mem::size_of::<u64>() * 8; // inbits
	let mut x: Vec<u64> = Vec::new();
	for segment in b.chunks(64){
		// warning: the last chunk might be shortert than 8
		// and load_be would pad it with zeros ON THE LEFT!!
		// but we need RIGHT PADDING
		let enc = if segment.len() < WORDSIZE {
			let mut topad = segment.to_owned();
			for _i in 0..WORDSIZE-segment.len(){
				topad.push(false);
			}
			topad.load_be()
		} else {
			segment.load_be()
		};

		x.push(enc)
	}
	x
}


/// turns a bitstream into chunks of u32
/// Note: the last byte will be right-padded if the encoding doesnt fill the netire byte
pub fn bits_to_fibonacci_u32array(b: &MyBitSlice) -> Vec<u32>{

    const WORDSIZE: usize = std::mem::size_of::<u32>() * 8; // inbits
	let mut x: Vec<u32> = Vec::new();
	for segment in b.chunks(32){
		// warning: the last chunk might be shortert than 8
		// and load_be would pad it with zeros ON THE LEFT!!
		// but we need RIGHT PADDING
		let enc = if segment.len() < WORDSIZE {
			let mut topad = segment.to_owned();
			for _i in 0..WORDSIZE-segment.len(){
				topad.push(false);
			}
			topad.load_be()
		} else {
			segment.load_be()
		};

		x.push(enc)
	}
	x
}

/// turns a bitstream into chunks of u8/u16/u32/u64
/// Note: the last byte will be right-padded if the encoding doesnt fill the netire byte
pub fn bits_to_fibonacci_generic_array<T:Integral>(b: &MyBitSlice) -> Vec<T>{

    // const WORDSIZE: usize = std::mem::size_of::<u32>() * 8; // inbits
    let wordsize = T::BITS as usize; // inbits

	let mut x: Vec<T> = Vec::new();
	for segment in b.chunks(wordsize){
		// warning: the last chunk might be shortert than 8
		// and load_be would pad it with zeros ON THE LEFT!!
		// but we need RIGHT PADDING
		let enc = if segment.len() < wordsize {
			let mut topad = segment.to_owned();
			for _i in 0..wordsize-segment.len(){
				topad.push(false);
			}
			topad.load_be()
		} else {
			segment.load_be()
		};

		x.push(enc)
	}
	x
}