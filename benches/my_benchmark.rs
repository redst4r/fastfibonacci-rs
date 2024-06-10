#![allow(missing_docs)]
use bitvec::order::Msb0;
use bitvec::slice::BitSlice;
use bitvec::vec::BitVec;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
// use fastfibonacci::bare_metal::decode_single_dirty;
use fastfibonacci::bit_decode::fast::{LookupVec, fast_decode, get_u8_decoder, get_u16_decoder};
use fastfibonacci::byte_decode::bare_metal_16single_faster::U16DecoderFast;
use fastfibonacci::byte_decode::bare_metal_64::Dirty64;
use fastfibonacci::byte_decode::byte_manipulation::{bits_to_fibonacci_generic_array, read_bit_u64};
use fastfibonacci::byte_decode::chunker::{U64BytesToU16, U64BytesToU64, U64BytesToU8};
use fastfibonacci::byte_decode::faster::{fast_decode_new, FastFibonacciDecoderNewU16, FastFibonacciDecoderNewU8, LookupVecNew, StreamType};
use fastfibonacci::bit_decode::fibonacci::{encode, FibonacciDecoder};
use fastfibonacci::byte_decode::u64_fibdecoder::U64Decoder;
use fastfibonacci::utils::random_fibonacci_stream;
use fastfibonacci::bit_decode::{MyBitSlice, MyBitVector};

use fastfibonacci::FastFibonacciDecoder;
use fibonacci_codec::Encode;
use rand::distributions::{Distribution, Uniform};

fn fibonacci_encode(c: &mut Criterion) {

    fn _dummy_bit_table(data: Vec<u64>) -> MyBitVector {
        encode(&data)
    }

    fn _dummy_fibonacci_codec(data: Vec<u64>) -> bit_vec::BitVec {
        data.fib_encode().unwrap()
    }

    let n = 1_000_000;
    let data_dist = Uniform::from(1..255);
    let mut rng = rand::thread_rng();
    let mut data: Vec<u64> = Vec::with_capacity(n);
    for _ in 0..n {
        data.push(data_dist.sample(&mut rng));
    }

    c.bench_function(
        &format!("Encoding: BitTable Fibonacci - {} elements", n),
        |b| b.iter(|| _dummy_bit_table(black_box(data.clone()))),
    );
    c.bench_function(&format!("Encoding: FibonacciCodec - {} elements", n), |b| {
        b.iter(|| _dummy_fibonacci_codec(black_box(data.clone())))
    });
}

// fn fibonacci_bitslice(c: &mut Criterion){
//     // let v: Vec<bool> = vec![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1].iter().map(|x|*x==1).collect();
//     let v: Vec<bool> = vec![1,0,1,0,1,0,1,1].iter().map(|x|*x==1).collect();
//     let bs: MyBitVector  = BitVec::from_iter(v.into_iter());

//     c.bench_function(
//         &format!("fib_bitslice"),
//         |b| b.iter(|| bitslice_to_fibonacci(black_box(&bs)))
//     );

//     c.bench_function(
//         &format!("fib_bitslice2"),
//         |b| b.iter(|| bitslice_to_fibonacci2(black_box(&bs)))
//     );

//     c.bench_function(
//         &format!("fib_bitslice3"),
//         |b| b.iter(|| bitslice_to_fibonacci3(black_box(&bs)))
//     );
//     c.bench_function(
//         &format!("fib_bitslice4"),
//         |b| b.iter(|| bitslice_to_fibonacci4(black_box(&bs)))
//     );
// }

fn fibonacci_decode(c: &mut Criterion) {
    // create a long fib string
    let seed = 23 ;
    let data = random_fibonacci_stream(1_000_000, 1, 10000, seed);
    // make a copy for fast decoder
    let mut data_fast: MyBitVector = BitVec::new();
    for bit in data.iter().by_vals() {
        data_fast.push(bit);
    }

    let table: LookupVec<u8> = LookupVec::new();
    let ground_truth = fast_decode(&data_fast, false, &table);

    // reference/baseline 
    fn _dummy_fibonacci_codec_decode(data: bit_vec::BitVec) -> Vec<u64> {
        let x = fibonacci_codec::fib_decode_u64(data)
            .map(|x| x.unwrap())
            .collect();
        x
    }

    let enc = ground_truth.fib_encode().unwrap();
    c.bench_function(&format!("Decoding: Fibonacci_Codec"), |b| {
        b.iter(|| _dummy_fibonacci_codec_decode(black_box(enc.clone())))
    });

    // =================================
    // FastFibonacci generic:
    // =================================
    let table8: LookupVec<u8> = LookupVec::new();
    c.bench_function(&format!("Decoding: generic fast vec u8-decode"), |b| {
        b.iter(|| fast_decode(black_box(&data_fast),false, &table8))
    });

    let table16: LookupVec<u16> = LookupVec::new();
    c.bench_function(&format!("Decoding: generic fast vec u16-decode"), |b| {
        b.iter(|| fast_decode(black_box(&data_fast),false, &table16))
    });

    // =================================
    // FastFibonacci: Iteratir
    // =================================
    fn dummy_fast_iter_u8(data_fast: &MyBitSlice) -> Vec<u64> {
        let f = get_u8_decoder(data_fast, false);
        let x: Vec<_> = f.collect();
        x
    }
    c.bench_function(&format!("Decoding: fast u8-Iterator"), |b| {
        b.iter(|| dummy_fast_iter_u8(black_box(&data_fast)))
    });


    fn dummy_fast_iter_u16(data_fast: &MyBitSlice) -> Vec<u64> {
        let f = get_u16_decoder(data_fast, false);
        let x: Vec<_> = f.collect();
        x
    }
    c.bench_function(&format!("Decoding: fast u16-Iterator"), |b| {
        b.iter(|| dummy_fast_iter_u16(black_box(&data_fast)))
    });

    // =================================
    // FibonacciDecoder: Iterator
    // =================================
    fn dummy(bv: MyBitVector) -> Vec<u64> {
        let dec = FibonacciDecoder::new(&bv, false);
        let x: Vec<_> = dec.collect();
        x
    }
    c.bench_function(&format!("Decoding: normal FibonacciDecoder"), |b| {
        b.iter(|| dummy(black_box(data.clone())))
    });
}

pub (crate) fn swap_endian(bytes: &[u8], wordsize: usize) -> Vec<u8>{
    let mut swapped_endian: Vec<u8> = Vec::with_capacity(bytes.len());
    for bytes in bytes.chunks(wordsize){
        swapped_endian.extend(bytes.iter().rev());
    }
    swapped_endian
}


fn fibonacci_mybitwise(c: &mut Criterion) {

    let seed = 23; 
    let data_encoded = random_fibonacci_stream(100_000, 1, 10000, seed);
    let mut x = bits_to_fibonacci_generic_array(&data_encoded);
    // this needs to have a multiiple of 8 bytes
    println!("{}", x.len());
    let bytse_to_add = 8 - (x.len() % 8);
    for _i in 0..bytse_to_add {
        x.push(0)
    }
    assert_eq!(x.len() % 8, 0);
    // x = swap_endian(&x, 8);

    let encoded_bytes = bits_to_fibonacci_generic_array(&data_encoded);
    let encoded_bytes64: Vec<_>= U64BytesToU64::new(encoded_bytes.as_slice()).collect();
    fn _dummy_dirty64(data: &[u64]) -> Vec<u64> {

        let mut decoded = Vec::with_capacity(100_000);
        let mut dd = Dirty64 {buf: &data, buf_size: data.len(), bitpos: 0, bufpos: 0};

        for _i in 0..100_000 {
            match dd.decode() {
                Ok(n) => { decoded.push(n); },
                Err(_e) => { assert_eq!(1,0); }
            }
        }
        decoded
    }
    c.bench_function(&format!("Decoding: bare metal 64 struct"), |b| {
        b.iter(|| _dummy_dirty64(black_box(&encoded_bytes64)))
    });


    // fn dummy_u64_iter(data: &[u8]) -> Vec<u64>{
    //     let dd = U64Decoder::new(data);
    //     let mut decoded: Vec<_> = Vec::with_capacity(100_000);

    //     for el in dd.take(100_000) {
    //         decoded.push(el)
    //     }
    //     decoded
    // }
    // c.bench_function(&format!("Decoding: U64Decoder"), |b| {
    //     b.iter(|| dummy_u64_iter(black_box(&x)))
    // });

    let bytes = bits_to_fibonacci_generic_array(&data_encoded);

    // new fast
    let table8: LookupVecNew<u8> = LookupVecNew::new();
    let x_u8: Vec<u8> = U64BytesToU8::new(bytes.as_slice()).collect();
    c.bench_function(&format!("Byte-fast-u8"), |b| {
        b.iter(|| fast_decode_new(black_box(x_u8.as_slice()),false, &table8))
    });

    let table16: LookupVecNew<u16> = LookupVecNew::new();
    let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).collect();
    c.bench_function(&format!("Byte-fast-u16"), |b| {
        b.iter(|| fast_decode_new(black_box(&x_u16),false, &table16))
    });

    c.bench_function(&format!("Byte-fast-u8-iterator"), |b| {
        b.iter(||  FastFibonacciDecoderNewU8::new(
            bytes.as_slice(), 
            &table8, 
            false, 
            StreamType::U64
        ).collect::<Vec<u64>>())
    });

    c.bench_function(&format!("Byte-fast-u16-iterator"), |b| {
        b.iter(||  FastFibonacciDecoderNewU16::new(
            bytes.as_slice(), 
            &table16, 
            false, 
            StreamType::U64
        ).collect::<Vec<u64>>())
    });


    // let mut x_u8_padded = x_u8.clone();
    // if x_u8_padded.len() % 2 == 1{
    //     x_u8_padded.push(0);
    // }

    // c.bench_function(&format!("Decoding: FAST NEW iterator u16"), |b| {
    //     b.iter(||  U16DecoderFast::new(x_u8_padded.as_slice(), &table16).collect::<Vec<u64>>())
    // });


    // make a copy for fast decoder
    let mut data_fast: MyBitVector = BitVec::new();
    for bit in data_encoded.iter().by_vals() {
        data_fast.push(bit);
    }

    let table8: LookupVec<u8> = LookupVec::new();
    c.bench_function(&format!("Bit-fast-u8"), |b| {
        b.iter(|| fast_decode(black_box(&data_fast),false, &table8))
    });

    let table16: LookupVec<u16> = LookupVec::new();
    c.bench_function(&format!("Bit-fast-u16"), |b| {
        b.iter(|| fast_decode(black_box(&data_fast),false, &table16))
    });

    c.bench_function(&format!("Bit-fast-u8-iterator"), |b| {
        b.iter(||  FastFibonacciDecoder::new(
            &data_encoded, 
            false, 
            &table8, 
        ).collect::<Vec<u64>>())
    });

    c.bench_function(&format!("Bit-fast-u16-iterator"), |b| {
        b.iter(||  FastFibonacciDecoder::new(
            &data_encoded, 
            false, 
            &table16, 
        ).collect::<Vec<u64>>())
    });


    fn dummy(bv: &MyBitSlice) -> Vec<u64> {
        let dec = FibonacciDecoder::new(bv, false);
        let x: Vec<_> = dec.collect();
        x
    }
    c.bench_function(&format!("Decoding: normal FibonacciDecoder"), |b| {
        b.iter(|| dummy(black_box(&data_encoded)))
    });
}


fn bitstore(c: &mut Criterion) {

    let seed = 23;
    let x = random_fibonacci_stream(100_000, 1, 10000, seed);
    let mut xu8: BitVec<u8, Msb0> = BitVec::new();
    let mut xu32: BitVec<u32, Msb0> = BitVec::new();
    let mut xu64: BitVec<u64, Msb0> = BitVec::new();
    for b in x.iter() {
        xu8.push(*b);
        xu32.push(*b);
        xu64.push(*b);
    }
    
    let bytes = bits_to_fibonacci_generic_array(&x);
    let u64array:Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
    fn dummy_u64raw(ua: &[u64]) -> usize {
        let mut s = 0_usize;
        for &u in ua {
            for i in 0..64 {
                let b = read_bit_u64(u, i);
                s += if b{ 1} else {0};
            }
        }
        s
    }

    fn dummy8(bv: &BitSlice<u8, Msb0>) -> usize {
        let mut s = 0_usize;
        for b in bv.iter().by_vals() {
            s += if b{ 1} else {0};
        }
        s
    }
    fn dummy32(bv: &BitSlice<u32, Msb0>) -> usize {
        let mut s = 0_usize;
        for b in bv.iter().by_vals() {
            s += if b{ 1} else {0};
        }
        s
    }

    fn dummy64(bv: &BitSlice<u64, Msb0>) -> usize {
        let mut s = 0_usize;
        for b in bv.iter().by_vals() {
            s += if b{ 1} else {0};
        }
        s
    }

    assert_eq!(
        dummy64(&xu64),
        dummy_u64raw(&u64array)
    );

    c.bench_function(&format!("u8 Store"), |b| {
        b.iter(|| dummy8(black_box(&xu8)))
    });

    c.bench_function(&format!("u32 Store"), |b| {
        b.iter(|| dummy32(black_box(&xu32)))
    });

    c.bench_function(&format!("u64 Store"), |b| {
        b.iter(|| dummy64(black_box(&xu64)))
    });

    c.bench_function(&format!("u64 raw"), |b| {
        b.iter(|| dummy_u64raw(black_box(&u64array)))
    });
}

// criterion_group!(benches, fibonacci_bitslice);
// fibonacci benchmarking

// criterion_group!(benches, fibonacci_encode, fibonacci_decode);
// criterion_group!(benches, fibonacci_decode);
criterion_group!(benches, fibonacci_mybitwise);
// criterion_group!(benches, bitstore);
criterion_main!(benches);
