//! 
//! 
use std::io::{self, BufRead, BufReader};
use std::io::{Error, Read};
use bitvec::slice::BitSlice;
use bitvec::vec::BitVec;
use bitvec::{bits, bitvec, field::BitField, order::{Lsb0, Msb0}};
use crate::{fastutils::FFBitorder, fibonacci::encode, utils::FIB64};


struct BitDec<'a> {
	buffer: &'a[u64],
	bitpos: usize,
	bufpos: usize,
	SIZE: usize, 
}


 impl <'a> BitDec<'a> {
	pub fn new(buf: &'a[u64]) -> Self {
		Self {buffer: buf, bitpos: 0, bufpos: 0, SIZE: 64}
	}

	pub fn decode_next(&mut self) -> u64{
		let mut i_fibo = 0_usize;  // the base in fib space

		// pos in buffer
		let mut buf_offset = self.bufpos;
		let mut bitshift = self.SIZE - (self.bitpos % self.SIZE) - 1;
		let mut num = 0;

		let mut bit = ((self.buffer[buf_offset] >> bitshift) & 1) as u64;
		let mut last_bit = 0;
		self.bitpos+=1;


		while last_bit + bit < 2 && buf_offset < self.buffer.len()
		{
			// println!("{counter}: {bit}");
			last_bit = bit;
			num += bit * (FIB64[i_fibo]);
			// println!("{num}");
	
			buf_offset = self.bufpos + self.bitpos / self.SIZE;
			bitshift = self.SIZE - (self.bitpos % self.SIZE) - 1;
	
			bit = ((self.buffer[buf_offset] >> bitshift) & 1) as u64;
	
			self.bitpos+=1;
			i_fibo+=1;
		}
	
		assert!(last_bit + bit == 2);
		assert!(buf_offset <= self.buffer.len());
	
		self.bufpos += self.bitpos / self.SIZE;
		self.bitpos %= self.SIZE;	

		return num	
	}
 }	

///
pub fn decode_single(buf: &[u64], mut bitpos: usize, mut bufpos: usize) -> (u64, usize, usize) {

	// bits per unit
	let SIZE = 64; //sizeof(T) * 8;
    let mut i_fibo = 0_usize;  // the base in fib space

	// pos in buffer
	let mut buf_offset = bufpos;
	let mut bitshift = SIZE - (bitpos % SIZE) - 1;
	// DEST_T num{0};
    let mut num = 0;

	let mut bit = ((buf[buf_offset] >> bitshift) & 1) as u64;
	let mut last_bit = 0;

	bitpos+=1;

	let mut counter = 0;
	while last_bit + bit < 2 && buf_offset < buf.len()
	{
		// println!("{counter}: {bit}");
		counter += 1;
		last_bit = bit;
		num += bit * (FIB64[i_fibo]);
		// println!("{num}");

		buf_offset = bufpos + bitpos / SIZE;
		bitshift = SIZE - (bitpos % SIZE) - 1;

		bit = ((buf[buf_offset] >> bitshift) & 1) as u64;

		bitpos+=1;
		i_fibo+=1;
		
	}

	assert!(last_bit + bit == 2);
	assert!(buf_offset <= buf.len());

	bufpos += bitpos / SIZE;
	bitpos %= SIZE;
	return (num, bitpos, bufpos);
}


#[test]
fn test_decode_next() {
	use crate::utils::bitstream_to_string;
	let the_ints = vec![1,2,3,4,5,6,7,8,9,10,11,12,13];
	let b = encode(&the_ints);
	println!("{}", bitstream_to_string(&b));
	let encoded: u64 = b[..64].load_be();

	let x = vec![encoded];

	let mut dec = BitDec::new(&x);
	for i in 0..the_ints.len() {
		let y = dec.decode_next();
		println!("dec : {y}, bitpos {}, bufpos {}", dec.bitpos, dec.bufpos);
	}
}


#[test]
fn test_decode() {

	// let bits = bits![u64, Msb0; 
	// 	0,0,0,0,0,0,1,1,
	// 	1,1,0,0,0,0,1,1,
	// 	0,0,0,0,0,0,0,0,
	// 	0,0,0,0,0,0,0,0,
	// 	0,0,0,0,0,0,0,0,
	// 	0,0,0,0,0,0,0,0,
	// 	0,0,0,0,0,0,0,0,
	// 	0,0,0,0,0,0,0,0,
	// 	]
	// .to_bitvec();
	// let b: u64 = bits.load_be();

	// let encoded = vec![b];


	use crate::utils::bitstream_to_string;
	let the_ints = vec![5,1,4,8,10,5,1,4,8,10,5,1,4,8,10,5,1,4,8,10];
	let b = encode(&the_ints);
	println!("{}", bitstream_to_string(&b));
	let encoded: u64 = b[..64].load_be();

	let x = vec![encoded];

	let mut bitpos = 0;
	let mut bufpos = 0;
	while bufpos < x.len() {

		let (dec, _bitpos, _bufpos) = decode_single(&vec![encoded], bitpos, bufpos);
		bitpos = _bitpos;
		bufpos = _bufpos;
		println!("dec : {dec}, bitpos {bitpos}, bufpos {bufpos}");
	}
}





fn read_bit(x: u8, pos: usize, wordsize: usize) -> bool {
	let thebit = x >> (wordsize - 1 - pos) & 1;
	thebit>0
}

fn read_bit_u64(x: u64, pos: usize, wordsize: usize) -> bool {
	let thebit = x >> (wordsize - 1 - pos) & 1;
	thebit>0
}

#[derive(Debug)]
///
pub enum MyErrorType {
    /// 
    Truncated(Vec<u8>),
}

fn u8vec_to_u64vec(u8vec: Vec<u8>) -> Vec<u64>{

	assert_eq!(u8vec.len() % 8, 0);
	let n_elements = u8vec.len() / 8; // elemts for the real (u64) buffer
	let factor = 8; // 8 u8 elements per u64 element

	let mut target = Vec::with_capacity(n_elements);
	for seg in u8vec.chunks(factor) {
		let u: [u8; 8] =seg.try_into().unwrap();
		let x = u64::from_ne_bytes(u);
		target.push(x);
	}
	target
}


struct U64Reader<R: io::BufRead> {
    inner: R,
}

impl<R: io::BufRead> U64Reader<R> {
    pub fn new(inner: R) -> Self {
        Self{
            inner
        }
    }

	pub fn pop_inner(self) -> R{
		self.inner
	}

	fn get_inner(&mut self) -> &mut R {
		&mut self.inner
	}
}

impl<R: io::BufRead> Iterator for U64Reader<R> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buff: [u8; 8] = [0;8];
        self.inner.read_exact(&mut buff).ok()?;
        Some(u64::from_be_bytes(buff))
    }
}

#[test]
fn test_U64iter() {
	let x = vec![1_u8, 2,3,4,5,6,7,8];

	let r = BufReader::new(x.as_slice());
	let ur = U64Reader::new(r);

	let u64_vec= ur.collect::<Vec<u64>>();
	assert_eq!(u64_vec.len(), 1);
	assert_eq!(u64_vec, vec![72623859790382856]);
	
	println!("{:?}", u64_vec)
}


#[test]
fn test_U64iter_trailing() {
	let x = vec![1_u8, 2,3,4,5,6,7,8,9];

	let r = BufReader::new(x.as_slice());
	let mut ur = U64Reader::new(r);

	let number64= ur.next();
	assert_eq!(number64, Some(72623859790382856));
	
	let inner = ur.pop_inner();
	
	let mut remainder = Vec::new();
	for b in inner.bytes() {
		match  b {
			Ok(some_byte) => {remainder.push(some_byte)},
			Err(_) => {panic!("error")},
		}
	}
	assert_eq!(remainder, vec![9])
}


#[inline]
/// reads u64 from the stream into the given buffer. Might not fill the entire buffer!!
/// # Returns
/// - Ok(n): the number of u64 elements read: i.e. buffer[0..n] are filled
fn load_into_u64buffer(stream: &mut impl Read, buffer: &mut[u64]) -> Result<usize, MyErrorType>{

	// trying to fill a buffer of u64 with max N elements
	let mut bsize = 0; // keep track of the actual number of elements we were able to fill
	let mut tbuffer = [0_u8; std::mem::size_of::<u64>()];

	// try to read one element into each buffer position
	while bsize < buffer.len() {
		match stream.read(&mut tbuffer) {
			Ok(8) => {
				println!("8 bytes");
				// got 8 bytes, turn into u64 and add to buffer
				let el = u64::from_ne_bytes(tbuffer);
				buffer[bsize] = el;
				bsize += 1;
			},
			Ok(n) => {
				println!("{n} bytes");
				// got less than 8 bytes
				// we should probably return those bytes, in case we need them
				return Err(MyErrorType::Truncated(tbuffer[..n].to_vec()));
			}
			Err(_) => todo!(),
		}
	};
	return Ok(bsize);
}


///
pub struct BitDec2 <'a> {
	stream: Box<dyn Read+ 'a>,
	buffer: Vec<u64>,
	buffersize: usize,
	bitpos: usize,
	bufpos: usize,
	SIZE: usize, // 
}
impl <'a>BitDec2<'a> {
	///
	pub fn new(mut stream: impl Read +'a) -> Self {
		let mut bsize = 1024*10; // how many elements in the buffer

		let SIZE = 64;  // the size (number of bits) of a single element u8->8, u64 -> 64

		let mut buf = Vec::with_capacity(bsize*8);
		for _i in 0..bsize*8 {
			buf.push(0);
		}

		let mut real_buf= Vec::new();
		for _ in 0..bsize {
			real_buf.push(0_u64);
		}
		
		match load_into_u64buffer(&mut stream, &mut real_buf) {
			Ok(n_el) => {
				bsize = n_el;
			},
			Err(e) =>  panic!("eror filling the buffer"),
		}

		Self {stream: Box::new(stream), buffer: real_buf, buffersize: bsize, bitpos: 0, bufpos: 0, SIZE:SIZE}
	}

	#[inline]
	fn load_into_buffer(&mut self) -> Result<(), MyErrorType>{

		// TODO: clear the buffer; not really neccessaty, but looks cleaner
		self.buffer.fill(0_u64);
		match load_into_u64buffer(&mut self.stream, &mut self.buffer) {
			Ok(n_el) => {
				self.buffersize = n_el;
				Ok(())
			},
			Err(MyErrorType::Truncated(trailing_bytes)) => {
				Err(MyErrorType::Truncated(trailing_bytes))
			},
		}
	}

	///
	#[inline]
	pub fn decode(&mut self) -> u64 {


		let mut num = 0;
		let mut i_fibo = 0;
		
		let mut bit = read_bit_u64(self.buffer[self.bufpos], self.bitpos, self.SIZE);
		let mut last_bit = false;
	
		self.bitpos = (self.bitpos + 1) % self.SIZE;
		if self.bitpos == 0 {
			self.bufpos += 1
		}
	
		// if we're done with the current buffer, read in more bytes
		if self.bufpos == self.buffersize {
			match self.load_into_buffer() {
				Ok(_) => {},
				Err(MyErrorType::Truncated(trailing_bytes)) => {
					todo!()
				},
			} 
		}
	
		while !(last_bit && bit) && self.bufpos <= self.buffersize {
			// 0 <= self.bufpos < bufsize if EOF is not reached
			// 0 <= self.bitpos < self.SIZE
			num += (bit as u64) * FIB64[i_fibo];
			i_fibo += 1;
	
			last_bit = bit;
			bit = read_bit_u64(self.buffer[self.bufpos], self.bitpos, self.SIZE);
			// println!("{:?} --- BufPos:{} BitPos{} -> {num}", self.buffer, self.bufpos, self.bitpos );


			self.bitpos = (self.bitpos + 1) % self.SIZE;
			if self.bitpos == 0 {
				// println!("INCREAMENT {}", self.bufpos);
				self.bufpos += 1;
				// println!("INCREAMENT {}", self.bufpos);
			};
	
			if self.bufpos >= self.buffersize {
				match self.load_into_buffer() {
					Ok(_) => {},
					Err(MyErrorType::Truncated(trailing_bytes)) => {
						todo!()
					},
				} 			}
		}

		if last_bit && bit {
			num
		} else {
			0
		}

	}
}


fn decodeFibonacciStream(
	// SRC_T *buf,
	// size_t &bufsize,
	// size_t &bitpos,
	// size_t &bufpos,
	// std::istream &in)
	mut bitpos: usize,
	mut bufpos: usize,
	mut input_stream: impl Read,
) -> u64
{

	let mut bufsize = 8;  // this can actually be smaller later on when we refill the buffer
	let mut buffer = [0_u8; 8];  // we read from the stream into here and decode from this buffer

	if let Ok(n) = input_stream.read(&mut buffer){
		// assert_eq!(n, 8)
		bufsize = n;
	} else {
		panic!("WFT")
	}


	let mut num = 0;
	let mut i_fibo = 0;

	let wordsize = 8;
	// let buf_offset = bufpos;
	// let bit_offset = wordsize - bitpos%wordsize -1;



	let mut bit = read_bit(buffer[bufpos], bitpos, wordsize);
	let mut last_bit = false;

	bitpos = (bitpos + 1) % wordsize;
	bufpos += if bitpos == 0 {1} else {0};

	// if we're done with the current buffer, read in more bytes
	if bufpos == bufsize
	{
		// in.read((char *)buf, sizeof(SRC_T) * bufsize);
		if let Ok(n) = input_stream.read(&mut buffer) {
			
			// bufsize = in.gcount() / sizeof(SRC_T);  // this is size in bytes, ie sizeof(u8) = 1
			bufsize = n; 
			bufpos = 0;
		} else {
			panic!("WTF")
		}

	}

	while !(last_bit && bit) && bufpos <= bufsize
	{
		// 0 <= bufpos < bufsize if EOF is not reached
		// 0 <= bitpos < wordsize
		println!("{buffer:?} --- {bufpos} {bitpos} -> {num}");
		num += (bit as u64) * FIB64[i_fibo];
		i_fibo += 1;

		last_bit = bit;
		bit = read_bit(buffer[bufpos], bitpos, wordsize);
		bitpos = (bitpos + 1) % wordsize;
		bufpos += if bitpos == 0 {1} else {0};

		if bufpos >= bufsize
		{
			// in.read((char *)buf, sizeof(SRC_T) * bufsize);
			if let Ok(n) = input_stream.read(&mut buffer) {
				
				// bufsize = in.gcount() / sizeof(SRC_T);  // this is size in bytes, ie sizeof(u8) = 1
				bufsize = n; 
				bufpos = 0;
			} else {
				panic!("WTF")
			}
		}
	}

	if last_bit && bit {
		num
	} else {
		0
	}
}

#[test]
fn test_decode_nex2s() {
	use crate::utils::bitstream_to_string;
	let the_ints = vec![1,2,3,4,5,6,7,8,9,10,11,12,13, 14];
	let b = encode(&the_ints);
	println!("{}", bitstream_to_string(&b));

	let mut x = Vec::new();
	for segment in b.chunks(8){
		let enc: u8 = segment.load_be();
		x.push(enc)
	}
	println!("x: {x:?}");


	// let bitpos = 0;
	// let bufpos = 0;
	// let r = decodeFibonacciStream(bitpos, bufpos, x.as_slice());
	// println!("{r} -- {bitpos} {bufpos}")

	let mut D = BitDec2::new(x.as_slice());


	let mut decoded = vec![];
	for _i in 0..the_ints.len() {
		let r = D.decode();
		decoded.push(r);
		println!("{r} -- BufPos {} BitPos {}", D.bufpos, D.bitpos);
	}
	assert_eq!(decoded, the_ints);
}




#[derive(Debug)]
///
pub enum MyErrorType3 {
    /// 
    TruncatedU64,
}

#[derive(Debug, Eq, PartialEq)]
/// 
pub struct PartialDecode{
	///
	pub num: u64,
	///
	pub i_fibo: usize
}
///
#[derive(Debug, Eq, PartialEq)]
pub enum DecodeError {
	/// the stream terminated, but not in `11` (the fibonacci terminator)
	PartiallyDecoded(PartialDecode),
	
	//
	// NoMoreU64(PartialDecode)
}
///
pub struct BitDec3 <R:BufRead> {
	u64stream: U64Reader<R>, //TODO clean
	buffer: u64,  // the current u64 to process bit by bit
	bitpos: usize,
	SIZE: usize, // 
	// last_bit: bool
}
impl <R:BufRead> BitDec3<R> {
	///
	pub fn new(stream: R) -> Self {

		// let ur = U64Reader::new(
		// 	BufReader::new(stream)
		// );
		let mut ur = U64Reader::new(stream);
		let buffer = ur.next().expect("not a single u64 in stream");
		// let buffer = 0_u64;  //dangerous, not really a value, should be None

		Self {u64stream: ur, buffer: buffer, bitpos: 0, SIZE: 64}
	}

	fn load_into_buffer(&mut self) -> Result<(), MyErrorType3>{
		println!("Loading into buffer");
		match self.u64stream.next(){
			Some(el) => {
				println!("\t Loaded {el}");

				self.buffer = el;
				Ok(())
			},
			None => {
			println!("\t Truncated");

				// no more u64 elements, but probably something trailing in the stream
				Err(MyErrorType3::TruncatedU64)
			},
		}
	}

	/// decodes a single number from thte stream
	/// no handlign of incompletes!
	/// use .decode() isntead
	#[inline]
	fn decode_internal(&mut self) -> Result<u64, DecodeError> {


		let mut num = 0;
		let mut i_fibo = 0;

		let mut bit = read_bit_u64(self.buffer, self.bitpos, self.SIZE);
		let mut last_bit = false;
	
		self.bitpos = (self.bitpos + 1) % self.SIZE;
		if self.bitpos == 0 {
			match self.load_into_buffer() {
				Ok(_) => {},
				Err(MyErrorType3::TruncatedU64) => {
					return Err(DecodeError::PartiallyDecoded(PartialDecode { num, i_fibo}))
				},
			}
		}
	
		while !(last_bit && bit) {
			// 0 <= self.bufpos < bufsize if EOF is not reached
			// 0 <= self.bitpos < self.SIZE
			// increment number
			num += (bit as u64) * FIB64[i_fibo];
			i_fibo += 1;
			println!("{} {bit} --- BitPos {} -> {num}", last_bit, self.bitpos );

			last_bit = bit;
			//the update: pull in a new bit, increment number
			bit = read_bit_u64(self.buffer, self.bitpos, self.SIZE);

			// advance bit psotision
			self.bitpos = (self.bitpos + 1) % self.SIZE;
			
			if self.bitpos == 0 { // we just processed 64 bits, i.e. we have to get a new u64 from sstream
				match self.load_into_buffer() {
					Ok(_) => {},
					Err(MyErrorType3::TruncatedU64) => {
						return Err(DecodeError::PartiallyDecoded(PartialDecode { num, i_fibo}))
					},
				}
			};
		}

		if last_bit && bit {
			Ok(num)
		} else {
			panic!("Cant happen");
			Err(DecodeError::PartiallyDecoded(
				PartialDecode { num, i_fibo}
			))
		}
	}

	/// 
	pub fn decode(&mut self) -> Option<u64> {
		match self.decode_internal() {
			Ok(n) => Some(n),

			// partial decoding:
			// either:
			// 1. we pulled in the last u64 of the stream (stream is empty), but it didnt terminate with `11` -> jsut return the unfinished reso
			// 2. we tried to pull another u64, but there;s less than 8 bytes in the stream
			Err(DecodeError::PartiallyDecoded(partial)) => {
				// partially read the bytes of the stream (we couldnt get a full u64, so it must fit here)
				let mut buffer = [0_u8; 8];  
				let inner = self.u64stream.get_inner();
				match inner.read(&mut buffer) {
						Ok(0) => {
							// case 1: we really pulled out every byte already
						},
						Ok(n) => {
							// case 2: some more bytes remaining, maybe contains a terminator
							
						}
						Err(_) => todo!(),
					}

				todo!()
			},
		}
	}

}





use crate::utils::bitstream_to_string;

///
pub fn bits_to_fibonacci_bytes(b: &BitSlice<u8, Msb0>) -> Vec<u8>{

	let mut x = Vec::new();
	for segment in b.chunks(8){
		// warning: the last chunk might be shortert than 8
		// and load_be would pad it with zeros ON THE LEFT!!
		// but we need RIGHT PADDING
		let enc = if segment.len() <8 {
			let mut topad = segment.to_owned();
			for _i in 0..8-segment.len(){
				topad.push(false);
			}
			topad.load_be()
		} else {
			segment.load_be()
		};

		x.push(enc)
	}
	return x
}
///
pub fn int_to_fibonacci_bytes(the_ints: &[u64])  -> Vec<u8>{
	let b = encode(&the_ints);
	dbg!(&b);
	bits_to_fibonacci_bytes(&b)
}

#[test]
fn test_decode_nex3s() {
	let the_ints = vec![1,2,3,4,5,6,7,8,9,10,11,12];
	let  x = int_to_fibonacci_bytes(&the_ints);


	let mut D = BitDec3::new(x.as_slice());


	let mut decoded = vec![];
	for _i in 0..the_ints.len() {
		match D.decode_internal(){
			Ok(r) => {
				decoded.push(r)
			}
				,
			Err(DecodeError::PartiallyDecoded(trunc)) => {
				println!("Partial decode: num: {}, ifib {}",  trunc.num, trunc.i_fibo);
			},
		}
		;
	}
	assert_eq!(decoded, the_ints);
}