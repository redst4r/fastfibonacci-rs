#![allow(missing_docs)]
use bitvec::order::Msb0;
use bitvec::slice::BitSlice;
use bitvec::vec::BitVec;
use bitvec::view::BitView;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fastfibonacci::bare_metal::decode_single_dirty;
use fastfibonacci::bare_metal_64::{bits_to_fibonacci_u64array, read_bit_u64, Dirty64};
use fastfibonacci::fast::{LookupVec, fast_decode, get_u8_decoder, get_u16_decoder};
use fastfibonacci::fibonacci::{encode, FibonacciDecoder};
use fastfibonacci::nobitvec::{bits_to_fibonacci_bytes};
use fastfibonacci::utils::random_fibonacci_stream;
use fastfibonacci::{MyBitSlice, MyBitVector};
// use fastfibonacci::random_fibonacci_stream;
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
    let data = random_fibonacci_stream(1_000_000, 1, 10000);
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

fn fibonacci_mybitwise(c: &mut Criterion) {

    let data_encoded = random_fibonacci_stream(100_000, 1, 10000);
    let x = bits_to_fibonacci_bytes(&data_encoded);

    fn _dummy(data: &[u8]) -> Vec<u64> {

        let mut decoded = Vec::with_capacity(100_000);

        let mut bitpos = 0;
        let mut bufpos = 0;
        let mut num = 0;
        let mut i_fibo = 0;

        for _i in 0..100_000 {
            match decode_single_dirty(&data, data.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo) {
                Ok(()) => {/* */},
                Err(e) => {
                    // println!("{:?}", e);
                    // println!("{_i}");
                    assert_eq!(1,0);
                }
            }
            // decode_single_dirty(data, data.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
            decoded.push(num);

            // reset
            num = 0;
            i_fibo = 0;
        }

        decoded
    }
    c.bench_function(&format!("Decoding: bare metal"), |b| {
        b.iter(|| _dummy(black_box(&x)))
    });


    let encoded_bytes64 = bits_to_fibonacci_u64array(&data_encoded);

    // fn _dummy64(data: &[u64]) -> Vec<u64> {

    //     let mut decoded = Vec::with_capacity(100_000);

    //     let mut bitpos = 0;
    //     let mut bufpos = 0;
    //     let mut num = 0;
    //     let mut i_fibo = 0;
    //     let mut last_bit = 0;
    //     for _i in 0..100_000 {
    //         match decode_single_dirty_64(&data, data.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo, &mut last_bit) {
    //             Ok(()) => {/* */},
    //             Err(e) => {
    //                 // println!("{:?}", e);
    //                 // println!("{_i}");
    //                 assert_eq!(1,0);
    //             }
    //         }
    //         // decode_single_dirty_64(data, data.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
    //         decoded.push(num);

    //         // reset
    //         num = 0;
    //         i_fibo = 0;
    //         last_bit = 0;
    //     }

    //     decoded
    // }
    // c.bench_function(&format!("Decoding: bare metal 64"), |b| {
    //     b.iter(|| _dummy64(black_box(&encoded_bytes64)))
    // });

    fn _dummyDirty64(data: &[u64]) -> Vec<u64> {

        let mut decoded = Vec::with_capacity(100_000);
        let mut D = Dirty64 {buf: &data, buf_size: data.len(), bitpos: 0, bufpos: 0};

        for _i in 0..100_000 {
            match D.decode() {
                Ok(n) => {
                    decoded.push(n);
                },
                Err(_e) => {
                    // println!("{:?}", e);
                    // println!("{_i}");
                    assert_eq!(1,0);
                }
            }
            // decode_single_dirty_64(data, data.len(), &mut bitpos, &mut bufpos, &mut num, &mut i_fibo).unwrap();
        }

        decoded
    }
    c.bench_function(&format!("Decoding: bare metal 64 struct"), |b| {
        b.iter(|| _dummyDirty64(black_box(&encoded_bytes64)))
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

    let x = random_fibonacci_stream(100_000, 1, 10000);
    let mut xu8: BitVec<u8, Msb0> = BitVec::new();
    let mut xu32: BitVec<u32, Msb0> = BitVec::new();
    let mut xu64: BitVec<u64, Msb0> = BitVec::new();
    for b in x.iter() {
        xu8.push(*b);
        xu32.push(*b);
        xu64.push(*b);
    }
    
    let u64array = bits_to_fibonacci_u64array(&x);
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
// criterion_group!(benches, fibonacci_mybitwise);
criterion_group!(benches, bitstore);
criterion_main!(benches);
