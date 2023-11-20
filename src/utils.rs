//!
//!
use crate::fibonacci::encode;
use crate::MyBitVector;
use bitvec::{store::BitStore, order::BitOrder, slice::BitSlice};
use itertools::Itertools;
use rand::{distributions::Uniform, prelude::Distribution};
use std::collections::HashMap;

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

// let v: Vec<_> = iterative_fibonacci().take(65 - 1).collect();
// println!("{:?}", v);
/// All fibonacci numbers up to 64bit
pub const FIB64: &[u64] = &[
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


/// Generates a random stream of interger in `[min,max]` and return the Fibonacci
/// encoding of thise stream
pub fn random_fibonacci_stream(n_elements: usize, min: usize, max: usize) -> MyBitVector {
    let data_dist = Uniform::from(min..max);
    let mut rng = rand::thread_rng();
    let mut data: Vec<u64> = Vec::with_capacity(n_elements);
    for _ in 0..n_elements {
        data.push(data_dist.sample(&mut rng) as u64);
    }
    encode(&data)
}


/// just for debugging purpose
pub fn bitstream_to_string<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>) -> String {
    let s = buffer.iter().map(|x| if *x { "1" } else { "0" }).join("");
    s
}

