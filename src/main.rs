//! ddd
// use std::time::Instant;

// use fastfibonacci::{utils::bits_to_fibonacci_bytes, utils::random_fibonacci_stream};

use std::time::Instant;
use fastfibonacci::{byte_decode::{bare_metal_16single_faster::U16DecoderFast, bare_metal_generic_single::U64DecoderGeneric, byte_manipulation::bits_to_fibonacci_generic_array, chunker::{U64BytesToU16, U64BytesToU8}, faster::{fast_decode_new, FastFibonacciDecoderNewU16, FastFibonacciDecoderNewU8, LookupVecNew}}, FastFibonacciDecoder, U64Decoder};
use fastfibonacci::bit_decode::fast::{fast_decode, LookupVec};
use fastfibonacci::utils::random_fibonacci_stream;

///
pub fn main() {

    // let n = 50_000_000;
    let n = 10_000_000;
    let data = random_fibonacci_stream(n, 1, 10000, 23);

    // regular U64Decode
    let bytes = bits_to_fibonacci_generic_array(&data);
    assert_eq!(bytes.len() % 8, 0);

    let table8: LookupVecNew<u8> = LookupVecNew::new();
    let table16: LookupVecNew<u16> = LookupVecNew::new();

    // // ------------------
    // // U64 DECODER
    // // ------------------
    // let now = Instant::now();
    // let dd = U64Decoder::new(bytes.as_slice());
    // let x: Vec<_> = dd.collect();
    // let elapsed_time = now.elapsed();
    // println!("U64Decoder: {} in {:?}", x.len(), elapsed_time);

    // // ------------------
    // // U64 DECODER GENERIC
    // // ------------------
    // let now = Instant::now();
    // let dd = U64DecoderGeneric::new(bytes.as_slice());
    // let x: Vec<_> = dd.collect();
    // let elapsed_time = now.elapsed();
    // println!("U64DecoderGeneric: {} in {:?}", x.len(), elapsed_time);


    // // ------------------
    // // bit-decode: fast u8
    // // ------------------
    // let table: LookupVec<u8> = LookupVec::new();
    // let now = Instant::now();
    // let ground_truth = fast_decode(&data, false, &table);
    // let elapsed_time = now.elapsed();
    // println!("bit-fast_decode {} in {:?}", ground_truth.len(), elapsed_time);

    
    // // ------------------
    // // byte-decode: fast u8
    // // ------------------
    // let x_u8: Vec<_> = U64BytesToU8::new(bytes.as_slice()).flatten().collect();
    // let now = Instant::now();
    // let ground_truth = fast_decode_new(&x_u8, false, &table8);
    // let elapsed_time = now.elapsed();
    // println!("byte-fast u8 {} in {:?}", ground_truth.len(), elapsed_time);

    // // ------------------
    // // byte-decode: fast u16
    // // ------------------
    // let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).flatten().collect();
    // let now = Instant::now();
    // let ground_truth = fast_decode_new(&x_u16, false, &table16);
    // let elapsed_time = now.elapsed();
    // println!("byte-fast u16 {} in {:?}", ground_truth.len(), elapsed_time);


    // ------------------
    // byte-decode: FastFibonacciDecoderNewU8
    // ------------------
    let now = Instant::now();
    let dd = FastFibonacciDecoderNewU8::new(bytes.as_slice(), &table8, false, fastfibonacci::byte_decode::faster::StreamType::U64);
    let x:Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("FastFibonacciDecoderNewU8 {} in {:?}", x.len(), elapsed_time);

    // ------------------
    // byte-decode: FastFibonacciDecoderNewU8
    // ------------------
    let now = Instant::now();
    let dd = FastFibonacciDecoderNewU16::new(bytes.as_slice(), &table16, false, fastfibonacci::byte_decode::faster::StreamType::U64);
    let x:Vec<_> = dd.collect();
    let elapsed_time = now.elapsed();
    println!("FastFibonacciDecoderNewU16 {} in {:?}", x.len(), elapsed_time);


    // // ------------------
    // // byte-decode: U16DecoderFast
    // // ------------------
    // let table16: LookupVecNew<u16> = LookupVecNew::new();
    // let now = Instant::now();
    // let dd = U16DecoderFast::new(bytes.as_slice(), &table16);
    // let x:Vec<_> = dd.collect();
    // let elapsed_time = now.elapsed();
    // println!("U16DecoderFast {} in {:?}", x.len(), elapsed_time);


    // // ------------------
    // // bit-decode: FastFibonacciDecoder<u8>
    // // ------------------
    // let table16: LookupVec<u8> = LookupVec::new();
    // let now = Instant::now();
    // let dd: FastFibonacciDecoder<u8> = FastFibonacciDecoder::new(&data, false, &table16);
    // let x:Vec<_> = dd.collect();
    // let elapsed_time = now.elapsed();
    // println!(" Bit-FastFibonacciDecoder<u8> {} in {:?}", x.len(), elapsed_time);

    // // ------------------
    // // bit-decode: FastFibonacciDecoder<u16>
    // // ------------------    
    // let table16: LookupVec<u16> = LookupVec::new();
    // let now = Instant::now();
    // let dd: FastFibonacciDecoder<u16> = FastFibonacciDecoder::new(&data, false, &table16);
    // let x:Vec<_> = dd.collect();
    // let elapsed_time = now.elapsed();
    // println!(" Bit-FastFibonacciDecoder<u16> {} in {:?}", x.len(), elapsed_time);


}

