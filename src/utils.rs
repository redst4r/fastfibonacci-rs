//! Utility functions
use bitvec::{order::BitOrder, slice::BitSlice, store::BitStore};
use itertools::Itertools;
use rand::{distributions::{Distribution, Uniform}, rngs::StdRng, SeedableRng};
use crate::{bit_decode::fibonacci::encode, bit_decode::MyBitVector};

/// Iterative fibonacci. just to get the first N fibonacci numbers
///
/// <https://github.com/rust-lang/rust-by-example>
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Iterator for Fibonacci {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        let new_next = self.curr + self.next;

        self.curr = self.next;
        self.next = new_next;

        Some(self.curr)
    }
}
/// A "constructor" for Iterative fibonacci.
#[allow(dead_code)] // only needed to generate the fibonacci sequence below
fn iterative_fibonacci() -> Fibonacci {
    Fibonacci { curr: 1, next: 1 }
}

/// All fibonacci numbers up to 64bit
const NFIBO:usize = 64;
pub (crate)  const FIB64: [u64; NFIBO] = {
    let mut seq = [0_u64; NFIBO];
    seq[0] = 1;
    seq[1] = 2;
    let mut k = 2;
    while k < NFIBO {
        seq[k] = seq[k-1] + seq[k-2];
        k += 1;
    }
    seq
};

#[test]
fn test_fconst(){
    let fib64_static: &[u64] = &[
        1,
        2,
        3,
        5,
        8,
        13,
        21,
        34,
        55,
        89,
        144,
        233,
        377,
        610,
        987,
        1597,
        2584,
        4181,
        6765,
        10946,
        17711,
        28657,
        46368,
        75025,
        121393,
        196418,
        317811,
        514229,
        832040,
        1346269,
        2178309,
        3524578,
        5702887,
        9227465,
        14930352,
        24157817,
        39088169,
        63245986,
        102334155,
        165580141,
        267914296,
        433494437,
        701408733,
        1134903170,
        1836311903,
        2971215073,
        4807526976,
        7778742049,
        12586269025,
        20365011074,
        32951280099,
        53316291173,
        86267571272,
        139583862445,
        225851433717,
        365435296162,
        591286729879,
        956722026041,
        1548008755920,
        2504730781961,
        4052739537881,
        6557470319842,
        10610209857723,
        17_167_680_177_565,
    ];
    assert_eq!(FIB64, fib64_static)
}

#[allow(dead_code)]
/// just for debugging purpose
pub (crate)fn bitstream_to_string<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>) -> String {
    let s = buffer.iter().map(|x| if *x { "1" } else { "0" }).join("");
    s
}

/// just for debugging purpose
pub fn bitstream_to_string_pretty<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>, chunksize: usize) -> String {

    // assert_eq!(buffer.len() % chunksize, 0);
    let mut the_strings = vec![];
    for chunk in buffer.chunks(chunksize).map(|c| c.iter().map(|x| if *x { "1" } else { "0" }).join("")) {
        the_strings.push(chunk);
    };
    the_strings.iter().join("|")
}

/// Create a random sequence of numbers, and encoded them via Fibonnaci. Used for testing.
pub fn random_fibonacci_stream(n_elements: usize, min: usize, max: usize, seed: u64) -> MyBitVector {
    
    let data_dist = Uniform::from(min..max);
    // let mut rng = thread_rng();
    let mut rng = StdRng::seed_from_u64(seed);
    let mut data: Vec<u64> = Vec::with_capacity(n_elements);
    for _ in 0..n_elements {
        data.push(data_dist.sample(&mut rng) as u64);
    }
    encode(&data)
}


/// a "wrapper" of the `bits!` macro except that we pin the BitStore and BitOrder  types
/// which somehow doesnt work for the macro
pub fn create_bitvector(bits: Vec<usize>) -> MyBitVector {

    // simpler:
    // let b: MyBitVector  = BitVec::from_iter(v.into_iter());

    let mut bitvector = MyBitVector::new();
    for b in bits {
        bitvector.push(b == 1);
    }
    bitvector
}