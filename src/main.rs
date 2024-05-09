//! ddd
// use std::time::Instant;

// use fastfibonacci::{utils::bits_to_fibonacci_bytes, utils::random_fibonacci_stream};

use std::time::Instant;
use fastfibonacci::{byte_decode::{bare_metal_16single_faster::U16DecoderFast, faster::{fast_decode_new, FastFibonacciDecoderNew, LookupVecNew}}, utils::bits_to_fibonacci_generic_array};
use fastfibonacci::bit_decode::fast::{fast_decode, LookupVec};
use fastfibonacci::utils::random_fibonacci_stream;

///
pub fn main() {

    let n = 50_000_000;
    let data = random_fibonacci_stream(n, 1, 10000, 23);

    let table: LookupVec<u8> = LookupVec::new();

    let now = Instant::now();
    let ground_truth = fast_decode(&data, false, &table);
    let elapsed_time = now.elapsed();
    println!("{} in {:?}", ground_truth.len(), elapsed_time);

    
    let table8: LookupVecNew<u8> = LookupVecNew::new();
    let x_u8 = bits_to_fibonacci_generic_array::<u8>(&data);

    let now = Instant::now();
    let ground_truth = fast_decode_new(&x_u8, false, &table8);
    let elapsed_time = now.elapsed();
    println!("{} in {:?}", ground_truth.len(), elapsed_time);


    // let x_u8 = bits_to_fibonacci_generic_array::<u8>(&data);
    let now = Instant::now();
    let dd = FastFibonacciDecoderNew::new(x_u8.into_iter(), &table8, false);
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

