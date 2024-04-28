pub fn decode_single_dirty_64(
	buf: &[u64], 
	buf_size: usize, 
	bitpos: &mut usize, 
	bufpos: &mut usize, 
	num: &mut u64, 
	i_fibo: &mut usize,
	last_bit: &mut u64,
) -> Result<(), DecodeError> {

	const WORDSIZE:usize = std::mem::size_of::<u64>() * 8; //sizeof(T) * 8;
	// let buf_offset = *bufpos;
	// let bit_offset = WORDSIZE - *bitpos % WORDSIZE -1;

	let mut bit = read_bit(buf[*bufpos], *bitpos) as u64;

	*bitpos = (*bitpos + 1) % WORDSIZE;
	if *bitpos == 0 {
		*bufpos += 1;
	}

	while *last_bit + bit < 2 && *bufpos < buf_size {
		*num += bit * FIB64[*i_fibo];
		*i_fibo += 1;
		*last_bit = bit;
		bit = read_bit(buf[*bufpos], *bitpos) as u64;

		*bitpos = (*bitpos +1) % WORDSIZE;

		if *bitpos == 0 {
			*bufpos += 1;
		}

		if *bufpos >= buf_size {
			return Err(DecodeError::PartiallyDecoded( PartialDecode { 
				num: *num + bit * FIB64[*i_fibo], 
				i_fibo: *i_fibo + 1, 
				last_bit: bit == 1  }))
		}
	}

	if *last_bit + bit < 2 {
		Err(DecodeError::PartiallyDecoded( PartialDecode { 
			num: *num + bit * FIB64[*i_fibo], 
			i_fibo: *i_fibo + 1, 
			last_bit: bit == 1  }))
	} else {
		Ok(())
	}
}


#[test]
fn test_correctness(){
    use crate::utils::test::random_fibonacci_stream;
    let N = 100000;
    // let N = 1000;
    let data_encoded = random_fibonacci_stream(N, 1, 10000);
	let encoded_bytes = bits_to_fibonacci_u64array(&data_encoded);
    // println!("Len: {}\n{}", data_encoded.len(), bitstream_to_string_pretty(&data_encoded, 64));
    // println!("{:?}", encoded_bytes);
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
	let mut last_bit = 0;
    for _i in 0..N {
        // println!("number: {_i}");
        match decode_single_dirty_64(
			&encoded_bytes, 
			encoded_bytes.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo, &mut last_bit) {
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
		last_bit = 0;
		// println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    }

    // ground thruth
    let dec = FibonacciDecoder::new(&data_encoded, false);
    let decoded_truth: Vec<_> = dec.collect();
    
    assert_eq!(decoded_truth, decoded);
}



#[test]
fn test_decode_overhang() {
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

	let buf_size = encoded.len();
	let mut bitpos = 0;
	let mut bufpos = 0;
	
	let mut num = 0 ;
	let mut i_fibo = 0;
	let mut last_bit = 0;
	assert_eq!(
		decode_single_dirty_64(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo, &mut last_bit),
		Ok(())
	);
	assert_eq!(last_bit, 1);
	assert_eq!(num, 4052739537881);

	// the trailing piece
	num = 0; // need to reset
	i_fibo = 0;
	last_bit = 0;
	let  r = decode_single_dirty_64(&encoded, buf_size, &mut bitpos, &mut bufpos, &mut num, &mut i_fibo, &mut last_bit);
	assert_eq!(
		r, 
		Err(DecodeError::PartiallyDecoded(PartialDecode { num: 2, i_fibo: 2, last_bit: true }))
	);

	//finishing the encoding
	let bits = create_bitvector(vec![ 
		1,0,0,0,0,0,0,0, //1 
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

	num = 2; // need to reset
	i_fibo = 2;
	last_bit = 1;
	bufpos = 0;
	bitpos=0;
	let  r = decode_single_dirty_64(
		&encoded, 
		encoded.len(), 
		&mut bitpos, 
		&mut bufpos, 
		&mut num, 
		&mut i_fibo, 
		&mut last_bit
	);
	assert_eq!(
		r, 
		Ok(())
	);
	assert_eq!(num, 2);


}


// pub struct FullDecoder {
// 	stream: u64
// }




// Nicer version of `decode_single_dirty_64` using a struct
// pub struct Dirty64_iter <'a> {
// 	///
// 	pub u64stream: u32,
// 	///
// 	pub buf: u64, 
// 	///
// 	pub buf_size: usize, 
// 	///
// 	pub bitpos: usize, 
// 	///
// 	pub bufpos: usize, 
// 	// num: u64, 
// 	// i_fibo: usize,
// }
// impl <'a> Dirty64_iter <'a> {

// 	/// decode a new number from the stream
// 	pub fn decode(&mut self) -> Result<u64, DecodeError> {
// 		self.decode_from_partial(0, 0, 0)
// 	}

// 	/// Decoding, starting from a previous partial decoding
// 	pub fn decode_from_partial(&mut self, mut num: u64, mut i_fibo: usize, mut last_bit: u64) -> Result<u64, DecodeError>{
// 		const WORDSIZE:usize = std::mem::size_of::<u64>() * 8; //sizeof(T) * 8;

// 		let mut bit = read_bit(self.buf[self.bufpos], self.bitpos) as u64;
// 		// let mut last_bit = 0;

// 		self.bitpos = (self.bitpos + 1) % WORDSIZE;
// 		if self.bitpos == 0 {
// 			self.bufpos += 1;
// 		}

// 		while last_bit + bit < 2 && self.bufpos < self.buf_size {
// 			num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
// 			i_fibo += 1;
// 			last_bit = bit;
// 			bit = read_bit(self.buf[self.bufpos], self.bitpos) as u64;

// 			self.bitpos = (self.bitpos +1) % WORDSIZE;

// 			if self.bitpos == 0 {
// 				self.bufpos += 1;
// 			}

// 			// TODO this should not be needed; covered by the loop cond and the after loop code
// 			if self.bufpos >= self.buf_size {
// 				return Err(DecodeError::PartiallyDecoded( PartialDecode { 
// 					num: num + bit * FIB64[i_fibo], // beed to increment, accounting for the 
// 					i_fibo: i_fibo + 1, 
// 					last_bit: bit == 1  
// 				}))
// 			}
// 		}

// 		if last_bit + bit < 2 {
// 			Err(DecodeError::PartiallyDecoded( PartialDecode { 
// 				num: num + bit* FIB64[i_fibo], 
// 				i_fibo: i_fibo + 1, 
// 				last_bit: bit == 1  
// 			}))
// 		} else {
// 			Ok(num)
// 		}
// 	}
// }
