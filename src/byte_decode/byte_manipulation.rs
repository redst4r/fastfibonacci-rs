//! This deals with the bare metal of reading single bits from
//! the fibonacci encoding
//! 
//! With the busfiles, here's the situation:
//! - A compressed busfile is just a stream of bytes.
//! - Those bytes need to be read in LittleEndian
//! - The bits in a byte need to be read LSB->MSB
//! For example, the fibbonacci encoding of the numbers [4,8] would be
//!   <--1-.-- <--2--.-
//! 0b00001101_00000011_00000000_00000000_00000000_00000000_00000000_00000000
//! 
//!  //          1st byte
//!                  |
//! a bytestream of [0, 0, 0, 0, 0, 0, 0, 88] (8 bytes of 6341068275337658368) 
//! should decode into the number 7!
//! 
//! //          fib  12358
//! in binary it is: 01011000_00000000000000000000000000000000000000000000000000000000
//!                   | |8  binary
//!                  64 16  
//! 
//! 
//! Similarly [0, 0, 0, 0, 0, 0, 192, 90] (u64: 6539226658941960192) encodes [7,7]:
//! 12357123 58
//! 01011010_11000000000000000000000000000000000000000000000000000000
//! 
use bitvec::field::BitField;
use crate::bit_decode::MyBitSlice;
use super::chunker::U64BytesToU64;


/// load a series of 8 bytes into a u64
/// 
/// Important to get the endianess correct here (needs to match the bus format)
pub (crate) fn load_u64_from_bytes(bytes: &[u8]) -> u64 {
	// with BE we need to swap the entire stream
	// u64::from_be_bytes(bytes.try_into().unwrap())
	
	// do le instead, i.e. the last byte `bytes[7]` is the first to be processed
	// This is how its done in the busfiles, and we need to stick to this!
	// u64::from_le_bytes(bytes.try_into().unwrap())

    // actually lets use the U64BytesToU64 for consistent fconversion
    U64BytesToU64::new(bytes).next().unwrap()
}

/// see xample at the top of the module
#[test]
fn test_load_u64_from_bytes() {
    assert_eq!(
        load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 0, 88]),
        6341068275337658368
    );

    assert_eq!(
        load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 0, 152]),
        10952754293765046272
    );

    assert_eq!(
        load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 192, 90]),
        6539226658941960192
    );
}

#[test]
fn test_decode_bits() {
    // this number corresponds to the following fibonacci bits
    // 12358...
    // 01011000
    let u = load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 0, 88]);
    assert_eq!(read_bit_u64(u, 0), false);
    assert_eq!(read_bit_u64(u, 1), true);
    assert_eq!(read_bit_u64(u, 2), false);
    assert_eq!(read_bit_u64(u, 3), true);
    assert_eq!(read_bit_u64(u, 4), true);
    assert_eq!(read_bit_u64(u, 5), false);
    assert_eq!(read_bit_u64(u, 6), false);
    assert_eq!(read_bit_u64(u, 7), false);

    // 1001100
    let u = load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 0, 152]);
    assert_eq!(read_bit_u64(u, 0), true);
    assert_eq!(read_bit_u64(u, 1), false);
    assert_eq!(read_bit_u64(u, 2), false);
    assert_eq!(read_bit_u64(u, 3), true);
    assert_eq!(read_bit_u64(u, 4), true);
    assert_eq!(read_bit_u64(u, 5), false);
    assert_eq!(read_bit_u64(u, 6), false);
    assert_eq!(read_bit_u64(u, 7), false);

    // 01011010_110
    let u = load_u64_from_bytes(&vec![0, 0, 0, 0, 0, 0, 192, 90]);
    assert_eq!(read_bit_u64(u, 0), false);
    assert_eq!(read_bit_u64(u, 1), true);
    assert_eq!(read_bit_u64(u, 2), false);
    assert_eq!(read_bit_u64(u, 3), true);
    assert_eq!(read_bit_u64(u, 4), true);
    assert_eq!(read_bit_u64(u, 5), false);
    assert_eq!(read_bit_u64(u, 6), true);
    assert_eq!(read_bit_u64(u, 7), false); 
    assert_eq!(read_bit_u64(u, 8), true); 
    assert_eq!(read_bit_u64(u, 9), true); 
}

/// Reads out the bits from a u64. Order is such that it's consistent with
/// the fibonacci encoding
#[inline]
pub fn read_bit_u64(x: u64, pos: usize) -> bool {
    read_bit_u64_msb(x, pos)
}

/// Reads out the bits, pos=0 will yield the MOST SIGNIFICANT BIT FIRST
/// see https://togglebit.io/posts/rust-bitwise/
#[inline]
fn read_bit_u64_msb(x: u64, pos: usize) -> bool {
	// assert!(pos < 64);
	const WORDSIZE:usize = std::mem::size_of::<u64>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}

/// Reads out the bits, pos=0 will yield the LEAST SIGNIFICANT BIT FIRST
/// see https://togglebit.io/posts/rust-bitwise/

#[inline]
fn read_bit_u64_lsb(x: u64, pos: usize) -> bool {
	// assert!(pos < 64);
	let shift_op = pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}

///
#[inline]
pub fn read_bit_u16(x: u16, pos: usize) -> bool {
    read_bit_u16_msb(x, pos)
}

/// Reads out the bits, pos=0 will yield the MOST SIGNIFICANT BIT FIRST
/// see https://togglebit.io/posts/rust-bitwise/
#[inline]
fn read_bit_u16_msb(x: u16, pos: usize) -> bool {
	// assert!(pos < 64);
	const WORDSIZE:usize = std::mem::size_of::<u16>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}

/// Reads out the bits, pos=0 will yield the LEAST SIGNIFICANT BIT FIRST
/// see https://togglebit.io/posts/rust-bitwise/

#[inline]
fn read_bit_u16_lsb(x: u16, pos: usize) -> bool {
	// assert!(pos < 64);
	let shift_op = pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}



///
#[inline]
pub fn read_bit_u32(x: u32, pos: usize) -> bool {
    read_bit_u32_msb(x, pos)
}

/// Reads out the bits, pos=0 will yield the MOST SIGNIFICANT BIT FIRST
/// see https://togglebit.io/posts/rust-bitwise/
#[inline]
fn read_bit_u32_msb(x: u32, pos: usize) -> bool {
	// assert!(pos < 64);
	const WORDSIZE:usize = std::mem::size_of::<u32>() * 8;
	let shift_op = WORDSIZE - 1 - pos;
	let thebit = (x >> shift_op) & 1;
	thebit>0
}


/// turns a bitstream into a u64/u32 representation
/// Note: the last byte will be right-padded if the encoding doesnt fill the netire byte
// pub fn bits_to_fibonacci_generic_array<T:Integral>(b: &MyBitSlice) -> Vec<T>{

//     // const WORDSIZE: usize = std::mem::size_of::<u32>() * 8; // inbits
//     let wordsize = T::BITS as usize; // inbits

// 	let mut x: Vec<T> = Vec::new();
// 	for segment in b.chunks(wordsize){
// 		// warning: the last chunk might be shortert than 8
// 		// and load_be would pad it with zeros ON THE LEFT!!
// 		// but we need RIGHT PADDING
// 		let enc = if segment.len() < wordsize {
// 			let mut topad = segment.to_owned();
// 			for _i in 0..wordsize-segment.len(){
// 				topad.push(false);
// 			}
// 			topad.load_be()  // REALLY ODD! we need to use bigEndian here, otherwise it doesnt not work out (see [bits_to_bytes] test)
// 		} else {
// 			segment.load_be()
// 		};

// 		x.push(enc)
// 	}
// 	x
// }

/// turns a bitstream into a u64/u32 representation
/// Note: the last byte will be right-padded if the encoding doesnt fill the netire byte
pub fn bits_to_fibonacci_generic_array(b: &MyBitSlice) -> Vec<u8>{

    // const WORDSIZE: usize = std::mem::size_of::<u32>() * 8; // inbits
    let wordsize = 64 as usize; // inbits

	let mut x: Vec<u8> = Vec::new();
	for segment in b.chunks(wordsize){
		// warning: the last chunk might be shortert than 8
		// and load_be would pad it with zeros ON THE LEFT!!
		// but we need RIGHT PADDING
		let enc:u64 = if segment.len() < wordsize {
			let mut topad = segment.to_owned();
			for _i in 0..wordsize-segment.len(){
				topad.push(false);
			}
			topad.load_be()  // REALLY ODD! we need to use bigEndian here, otherwise it doesnt not work out (see [bits_to_bytes] test)
		} else {
			segment.load_be()
		};
        
        for byte in enc.to_le_bytes(){
		    x.push(byte)
        }
	}
	x
}

#[cfg(test)]
mod testing {
    use crate::utils::create_bitvector;
    use super::*;
    #[test]
    fn bits_to_bytes() {
    
        // this is the number 7 in fibonacci
        let bits = create_bitvector(vec![
            0,1,0,1,1,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            ]);

        let bytes = bits_to_fibonacci_generic_array(&bits);
        assert_eq!(bytes, vec![0,0,0,0,0,0,0,88_u8]);

        let bytes = bits_to_fibonacci_generic_array(&bits);
        let xu64: Vec<_> = U64BytesToU64::new(bytes.as_slice()).collect();
        assert_eq!(xu64, vec![6341068275337658368]);
    
    
    }
    #[test]
    fn test_bits_to_bytes() {

        // assert that the first bit is the most significant per chunk
        let bits = create_bitvector(vec![
            1,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
        ]);

        assert_eq!(
            bits_to_fibonacci_generic_array(&bits),
            vec![0, 0, 0, 0, 0, 0, 0, 128]
        );

        // assert that things are padded correctly: if we cant fill the entire segment, append zero bytes     
        let bits = create_bitvector(vec![
            1,0,0,0,0,0,0,0,
        ]);        
        assert_eq!(
            bits_to_fibonacci_generic_array(&bits[..8]),
            vec![0, 0, 0, 0, 0, 0, 0, 128]
        );



        // assert that things are encoded as little endian: the first byte is the least significant     
        let bits = create_bitvector(vec![
            1,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
        ]); 
        assert_eq!(
            bits_to_fibonacci_generic_array(&bits),
            vec![0, 0, 0, 0, 0, 0, 0, 128]
        );
    }

    #[test]
    fn test_read_bit_msb() {
        assert_eq!(read_bit_u64_msb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), false, "0 pos 0");
        assert_eq!(read_bit_u64_msb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), false, "0 pos 1");
        assert_eq!(read_bit_u64_msb(0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), true, "2 pos 0");
        assert_eq!(read_bit_u64_msb(0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), false, "2 pos 1");
        assert_eq!(read_bit_u64_msb(0b01000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), false, "2 pos 1");
        assert_eq!(read_bit_u64_msb(0b01000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 1), true, "2 pos 1");
    }

    #[test]
    fn test_read_bit_lsb() {
        assert_eq!(read_bit_u64_lsb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 0), false);
        assert_eq!(read_bit_u64_lsb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000001, 0), true);
        assert_eq!(read_bit_u64_lsb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000010, 1), true);
        assert_eq!(read_bit_u64_lsb(0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_10000010, 7), true);
    }
}
