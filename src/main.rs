//! ddd
// use std::time::Instant;

// use fastfibonacci::{utils::bits_to_fibonacci_bytes, utils::random_fibonacci_stream};

use std::time::Instant;
use fastfibonacci::{byte_decode::{bare_metal_16single_faster::U16DecoderFast, bare_metal_generic_single::U64DecoderGeneric, byte_manipulation::bits_to_fibonacci_generic_array, faster::{fast_decode_new, FastFibonacciDecoderNewU8, LookupVecNew}}, U64Decoder};
use fastfibonacci::bit_decode::fast::{fast_decode, LookupVec};
use fastfibonacci::utils::random_fibonacci_stream;

///
pub fn main() {

    // let n = 50_000_000;
    let n = 500_000;
    let data = random_fibonacci_stream(n, 1, 10000, 23);

    // regular U64Decode
    let mut x_u8_padded = bits_to_fibonacci_generic_array::<u8>(&data);
    for i in 0..8 - (x_u8_padded.len() % 8) {
        x_u8_padded.push(0)
    }
    assert_eq!(x_u8_padded.len() % 8, 0);
    let now = Instant::now();
    let dd = U64Decoder::new(x_u8_padded.as_slice());
    let x: Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("U64Decoder: {} in {:?}", x.len(), elapsed_time);

    let now = Instant::now();
    let dd = U64DecoderGeneric::new(x_u8_padded.as_slice());
    let x: Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("U64DecoderGeneric: {} in {:?}", x.len(), elapsed_time);


    // fast bit decode
    let table: LookupVec<u8> = LookupVec::new();
    let now = Instant::now();
    let ground_truth = fast_decode(&data, false, &table);
    let elapsed_time = now.elapsed();
    println!("bit-fast_decode {} in {:?}", ground_truth.len(), elapsed_time);

    
    // fast byte decode
    let table8: LookupVecNew<u8> = LookupVecNew::new();
    let x_u8 = bits_to_fibonacci_generic_array::<u8>(&data);

    let now = Instant::now();
    let ground_truth = fast_decode_new(&x_u8, false, &table8);
    let elapsed_time = now.elapsed();
    println!("byte-fast{} in {:?}", ground_truth.len(), elapsed_time);


    let x_u8 = bits_to_fibonacci_generic_array::<u8>(&data);
    let now = Instant::now();
    let dd = FastFibonacciDecoderNewU8::new(x_u8.as_slice(), &table8, false, fastfibonacci::byte_decode::faster::StreamType::U64);
    let x:Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("{} in {:?}", x.len(), elapsed_time);


    let x_u8 = bits_to_fibonacci_generic_array::<u8>(&data);
    let table16: LookupVecNew<u16> = LookupVecNew::new();
    let now = Instant::now();
    let dd = U16DecoderFast::new(x_u8.as_slice(), &table16);
    let x:Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("{} in {:?}", x.len(), elapsed_time);
    // let now = Instant::now();
    // let f = get_u8_decoder(&data, false);
    // let x: Vec<_> = f.collect();
    // let elapsed_time: std::time::Duration = now.elapsed();
    // println!("{} in {:?}", x.len(), elapsed_time);


    // let now = Instant::now();
    // let xxx = decode(&data, false);
    // let elapsed_time: std::time::Duration = now.elapsed();
    // println!("{} in {:?}", xxx.len(), elapsed_time);
    
	// let encoded_bytes = bits_to_fibonacci_bytes(&data);
    // // let mut decoded = Vec::with_capacity(n);

    // let mut bitpos = 0;
    // let mut bufpos = 0;
    // let mut num = 0;
    // let mut i_fibo = 0;

    // for _i in 0..n {
    //     // println!("number: {_i}");
    //     decode_single_dirty(&encoded_bytes, encoded_bytes.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
    //     decoded.push(num);

    //     // reset
    //     num = 0;
    //     i_fibo = 0;
	// 	// println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    // }

}

