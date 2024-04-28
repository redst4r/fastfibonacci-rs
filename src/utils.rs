//! Utility functions
use bitvec::{store::BitStore, order::BitOrder, slice::BitSlice};
use itertools::Itertools;
use rand::{distributions::{Distribution, Uniform}, thread_rng};

use crate::{fibonacci::encode, MyBitVector};

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
pub (crate) const FIB64: &[u64] = &[
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

#[doc(hidden)]
#[cfg(test)]
pub mod test {
    use crate::MyBitVector;
    use rand::{distributions::Uniform, prelude::Distribution, thread_rng};
    use crate::fibonacci::encode;

    /// Generates a random stream of interger in `[min,max]` and return the Fibonacci
    /// encoding of thise stream
    pub fn random_fibonacci_stream(n_elements: usize, min: usize, max: usize) -> MyBitVector {
        let data_dist = Uniform::from(min..max);
        let mut rng = thread_rng();
        let mut data: Vec<u64> = Vec::with_capacity(n_elements);
        for _ in 0..n_elements {
            data.push(data_dist.sample(&mut rng) as u64);
        }
        encode(&data)
    }
}

#[allow(dead_code)]
/// just for debugging purpose
pub (crate)fn bitstream_to_string<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>) -> String {
    let s = buffer.iter().map(|x| if *x { "1" } else { "0" }).join("");
    s
}

// #[allow(dead_code)]
// /// just for debugging purpose
// pub (crate)fn bitstream_to_string_pretty<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>, chunksize: usize) -> String {

//     // assert_eq!(buffer.len() % chunksize, 0);

//     let mut the_strings = vec![];
//     for i in 0..buffer.len() / chunksize {
//         let chunk = &buffer[(i*chunksize)..(i+1)*chunksize];

//         let s = chunk.iter().map(|x| if *x { "1" } else { "0" }).join("");
//         the_strings.push(s);
//     };

//     if buffer.len() % chunksize != 0 {
//         println!("might be missing the end");
//     }
//     the_strings.iter().join("|")
// }

/// just for debugging purpose
pub fn bitstream_to_string_pretty<T: BitStore, O: BitOrder>(buffer: &BitSlice<T, O>, chunksize: usize) -> String {

    // assert_eq!(buffer.len() % chunksize, 0);
    let mut the_strings = vec![];
    for chunk in buffer.chunks(chunksize).map(|c| c.iter().map(|x| if *x { "1" } else { "0" }).join("")) {
        the_strings.push(chunk);
    };
    the_strings.iter().join("|")
}

///
pub fn random_fibonacci_stream(n_elements: usize, min: usize, max: usize) -> MyBitVector {
    let data_dist = Uniform::from(min..max);
    let mut rng = thread_rng();
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