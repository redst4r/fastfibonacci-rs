use bitvec::slice::BitSlice;
use bitvec::{prelude::Msb0, vec::BitVec};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fastfibonacci::fast_fib_generic::{LookupVec, fast_decode};
use fastfibonacci::fibonacci::{encode, FibonacciDecoder};
use fastfibonacci::fibonacci_fast::{
    fast_decode_u16, fast_decode_u8, FastFibonacciDecoder, LookupU16Vec, LookupU8Vec,
};
use fastfibonacci::fibonacci_old::fib_enc_multiple;
use fastfibonacci::random_fibonacci_stream;
use fibonacci_codec::Encode;
use rand::distributions::{Distribution, Uniform};

type MyBitVector = BitVec<u8, Msb0>;

fn fibonacci_encode(c: &mut Criterion) {
    fn _dummy_my_fib(data: Vec<u64>) -> MyBitVector {
        fib_enc_multiple(&data)
    }

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

    c.bench_function(&format!("Encoding: My Fibonacci - {} elements", n), |b| {
        b.iter(|| _dummy_my_fib(black_box(data.clone())))
    });

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

    let table = LookupU8Vec::new();
    let ground_truth = fast_decode_u8(data_fast.clone(), &table);

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

    // c.bench_function(
    //     &format!("fast decode"),
    //     |b| b.iter(|| fast_decode(black_box(data_fast.clone()), black_box(8)))
    // );

    // =================================
    // FastFibonacci:
    // =================================

    let table = LookupU8Vec::new();
    c.bench_function(&format!("Decoding: fast vec u8-decode"), |b| {
        b.iter(|| fast_decode_u8(black_box(data_fast.clone()), black_box(&table)))
    });

    let table = LookupU16Vec::new();
    c.bench_function(&format!("Decoding: fast vec u16-decode"), |b| {
        b.iter(|| fast_decode_u16(black_box(data_fast.clone()), black_box(&table)))
    });

    // =================================
    // FastFibonacci generic:
    // =================================
    let table8: LookupVec<u8> = LookupVec::new();
    c.bench_function(&format!("Decoding: generic fast vec u8-decode"), |b| {
        b.iter(|| fast_decode(black_box(data_fast.clone()),false, &table8))
    });

    let table16: LookupVec<u16> = LookupVec::new();
    c.bench_function(&format!("Decoding: generic fast vec u16-decode"), |b| {
        b.iter(|| fast_decode(black_box(data_fast.clone()),false, &table16))
    });

    // =================================
    // FastFibonacci: Iteratir
    // =================================
    fn dummy_fast_iter(data_fast: &BitSlice<u8, Msb0>) -> Vec<u64> {
        let f = FastFibonacciDecoder::new(data_fast.clone(), false);
        let x: Vec<_> = f.collect();
        x
    }
    c.bench_function(&format!("Decoding: fast Iterator"), |b| {
        b.iter(|| dummy_fast_iter(black_box(&data_fast.clone())))
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

// criterion_group!(benches, fibonacci_bitslice);
// fibonacci benchmarking
criterion_group!(benches, fibonacci_encode, fibonacci_decode);
criterion_main!(benches);
