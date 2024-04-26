//! Regular Fibonacci encoding and decoding of integers, going bit-by-bit.
//! See [here](https://en.wikipedia.org/wiki/Fibonacci_coding).
//!
//! # Usage
//! ```rust
//! // Encoding
//! use fastfibonacci::fibonacci::{encode, decode, FibonacciDecoder};
//! let encoded = encode(&vec![34, 12]) ;
//!
//! // Decoding
//! let decoded = decode(&encoded, false); // 2nd argument: shift all values by -1 (in case we wanted to encode 0 in the fibonacci encoding)
//! assert_eq!(decoded, vec![34,12]);
//! 
//! // Alternatively, we can also create an iterator (yields one decoded int at a time)
//! let f = FibonacciDecoder::new(&encoded, false);
//! assert_eq!(f.collect::<Vec<_>>(), vec![34,12])
//! ```

use num::CheckedSub;
use std::fmt::Debug;
use crate::utils::FIB64;
/// note the the entire content of this module is
/// **independent** of the choice of BitOrder, i.e.
/// both Lsb0 and Msb0 work the same way!
use crate::{MyBitSlice, MyBitVector, FbDec};


/// Decoder for Fibonacci encoded integer sequences (allows to iterate)
///
/// Constructed from a bufffer (a binary sequence) which is gradually processed
/// when iterating. The buffer remains unchanged, just the pointers into the buffer move.
///
/// # Example
/// ```rust
/// use fastfibonacci::{FbDec, fibonacci::FibonacciDecoder};
/// use bitvec::prelude::{BitVec, MyBitOrder};
/// let buffer:BitVec<u8, MyBitOrder> = BitVec::from_iter(vec![true, false, true, true, false, true, true, false, true]);
/// let d = FibonacciDecoder::new(buffer.as_bitslice(), false);
/// let mut results = vec![];
/// for decoded in d {
///     println!("{}", decoded);
///     results.push(decoded)
/// }
/// // Will print 4, 2
/// assert_eq!(results, vec![4, 2]);
/// 
/// ```

// TODO currently this is not possible, as the iterator gets consumed
// // Get the remaining bits in the buffer
// let leftover = d.get_remaining_buffer();
// let expected_leftover :BitVec<u8, MyBitOrder> = BitVec::from_iter(vec![false, true]);
// assert_eq!(leftover, expected_leftover);
#[derive(Debug)]
pub struct FibonacciDecoder<'a> {
    buffer: &'a MyBitSlice,
    current_pos: usize, // where we are at in the buffer (the last split), i.e the unprocessed part is buffer[current_pos..]
    shifted_by_one: bool, // if true, this means that a decoded value of `1` actually is a zero (and was shifted in the encoding)
}

impl<'a> FibonacciDecoder<'a> {
    /// Creates a new fibonacci decoder for the given buffer.
    /// This leaves the buffer  unchanged, just moves a pointer (`self.current_pos`) in the buffer around.
    pub fn new(buffer: &'a MyBitSlice, shifted_by_one: bool) -> Self {
        FibonacciDecoder {
            buffer,
            current_pos: 0,
            shifted_by_one,
        }
    }
}

impl<'a> FbDec<'a> for FibonacciDecoder<'a> {
    /// Returns the buffer behind the last bit processed.
    /// Comes handy when the buffer contains data OTHER than fibonacci encoded
    /// data that needs to be processed externally.
    fn get_remaining_buffer(&self) -> &'a MyBitSlice {
        &self.buffer[self.current_pos..]
    }

    /// How far did we process into the buffer (pretty much the first bit after a `11`).
    fn get_bits_processed(&self) -> usize {
        self.current_pos
    }
}

impl<'a> Iterator for FibonacciDecoder<'a> {
    type Item = u64;

    // #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut prev_bit = false;
        let mut accumulator = 0;
        let current_slice = &self.buffer[self.current_pos..];
        // println!("currentslice {:?}", current_slice);
        for (idx, current_bit) in current_slice.iter().by_vals().enumerate() {
            if idx > 64 {
                panic!("fib-codes cant be longer than 64bit, something is wrong!");
            }
            match (prev_bit, current_bit) {
                // current bit set, but not 11
                (false, true) => {
                    accumulator += FIB64[idx];
                }
                (true, true) => {
                    // found 11
                    let hit_len = idx + 1;
                    self.current_pos += hit_len;
                    if self.shifted_by_one {
                        return Some(accumulator - 1);
                    } else {
                        return Some(accumulator);
                    }
                }
                (false, false) | (true, false) => {} // current bit is zero, nothing to add
            }
            prev_bit = current_bit
        }
        None
    }
}

/// Slightly faster (2x) encoding of multiple integers into a bitvector via Fibonacci Encoding
pub fn encode(data: &[u64]) -> MyBitVector {
    // the capacity is a minimum, assuming each element of data is 1, i.e. `11` in fib encoding
    let mut overall = MyBitVector::with_capacity(2 * data.len());

    // this just appends to the `overall` bitvec
    for &x in data {
        bits_from_table_internal(x, FIB64, &mut overall).unwrap();
    }
    overall
}

/// Fibonacci-decodes the bitstream into integers.
/// 
/// *Note*: this only decodes to the last delimiter (`11`) and skip any trailing bits.
/// For examples if encoded=`011001` this will decode `011`, but will leave `001` untouched (as it is not proper fibonacci encoding).
/// 
/// # Parameters:
/// * encoded: bitstream to decode
/// * shifted_by_one: if true, subtracts 1 from each decoded number. In case the data was encoded after shifting (to allow 0 to be encoded)
pub fn decode(encoded: &MyBitSlice, shifted_by_one:bool) -> Vec<u64> {
    let dec = FibonacciDecoder::new(encoded, shifted_by_one);
    let x: Vec<u64> = dec.collect();
    x
    // if dec.get_remaining_buffer().is_empty() {
    //     Err(DecodeError::TrailingBits)
    // } else {
    //     Ok(x)
    // }
}

/// Hijacked from <https://github.com/antifuchs/fibonacci_codec>
#[derive(Debug, PartialEq)]
pub enum EncodeError<T>
where
    T: Debug + Send + Sync + 'static,
{
    /// Indicates an attempt to encode the number `0`, which can't be
    /// represented in fibonacci encoding.
    ValueTooSmall(T),

    /// A bug in fibonacci_codec in which encoding the contained
    /// number resulted in an attempt to subtract a larger fibonacci
    /// number than the number to encode.
    Underflow(T),
}

/// Error when decoding a fibonacci bitstream into integers
pub enum DecodeError
{
    /// Raised when decoding a buffer which does NOT terminate with `11`,
    /// i.e. there's some trailing bits
    TrailingBits
}


/// slightly faster fibonacci endocing (2x faster), taken from
/// <https://github.com/antifuchs/fibonacci_codec>
#[inline]
fn bits_from_table_internal<T>(
    n: T,
    table: &'static [T],
    result: &mut MyBitVector,
) -> Result<(), EncodeError<T>>
where
    T: CheckedSub + PartialOrd + Debug + Copy + Send + Sync + 'static,
{
    let mut current = n;
    let split_pos = table
        .iter()
        .rposition(|elt| *elt <= n)
        .ok_or(EncodeError::ValueTooSmall::<T>(n))?;

    let mut i = result.len() + split_pos + 1;
    // result.grow(split_pos + 2, false);

    result.resize(result.len() + split_pos + 2, false);
    result.set(i, true);
    for elt in table.split_at(split_pos + 1).0.iter().rev() {
        i -= 1;
        if elt <= &current {
            let next = match current.checked_sub(elt) {
                Some(next) => next,
                None => {
                    // We encountered an underflow. This is a bug, and
                    // I have no idea how it could even occur in real
                    // life. However, let's clean up and return a
                    // reasonable error:
                    result.truncate(split_pos + 2);
                    return Err(EncodeError::Underflow(n));
                }
            };
            current = next;
            result.set(i, true);
        };
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use crate::{fibonacci::{encode, FibonacciDecoder}, utils::create_bitvector};

    mod test_table {
        use crate::fibonacci::{bits_from_table_internal, encode, MyBitVector, FIB64};
        use bitvec::vec::BitVec;

        #[test]
        fn test_1() {
            let mut bv: MyBitVector = BitVec::new();
            bits_from_table_internal(1, FIB64, &mut bv).unwrap();
            assert_eq!(bv.iter().collect::<Vec<_>>(), vec![true, true]);
        }

        #[test]
        fn test_2() {
            let mut bv: MyBitVector = BitVec::new();
            bits_from_table_internal(2, FIB64, &mut bv).unwrap();
            assert_eq!(bv.iter().collect::<Vec<_>>(), vec![false, true, true]);
        }
        #[test]
        fn test_14() {
            let mut bv: MyBitVector = BitVec::new();
            bits_from_table_internal(14, FIB64, &mut bv).unwrap();
            assert_eq!(
                bv.iter().collect::<Vec<_>>(),
                vec![true, false, false, false, false, true, true]
            );
        }
        #[test]
        fn test_consecutive() {
            let mut bv: MyBitVector = BitVec::new();
            bits_from_table_internal(1, FIB64, &mut bv).unwrap();
            bits_from_table_internal(2, FIB64, &mut bv).unwrap();
            bits_from_table_internal(1, FIB64, &mut bv).unwrap();
            assert_eq!(
                bv.iter().collect::<Vec<_>>(),
                vec![true, true, false, true, true, true, true]
            );
        }

        #[test]
        fn test_encode() {
            let x = vec![1, 2, 3];
            let bv = encode(&x);
            assert_eq!(
                bv.iter().collect::<Vec<_>>(),
                vec![true, true, false, true, true, false, false, true, true]
            );
        }

        #[test]
        fn test_encode_single_item() {
            let x = vec![3];
            let bv = encode(&x);
            assert_eq!(
                bv.iter().collect::<Vec<_>>(),
                vec![false, false, true, true]
            );
        }
    }

    #[test]
    fn test_encode_mutiple() {
        let enc = encode(&vec![1, 14]);
        assert_eq!(
            enc.iter().collect::<Vec<_>>(),
            vec![true, true, true, false, false, false, false, true, true]
        );
    }

    // #[test]
    // #[should_panic(expected = "n must be positive")]
    // fn test_fib_encode_0() {
    //     fib_enc(0);
    // }
    // #[test]
    // #[should_panic(expected = "n must be smaller than max fib")]
    // fn test_fib_encode_u64max() {
    //     fib_enc(u64::MAX);

    // }


    #[test]
    fn test_myfib_decoder() {
        use crate::utils::create_bitvector;
        // let v: Vec<bool> = vec![0,0,1,1].iter().map(|x|*x==1).collect();
        // let b: MyBitVector  = BitVec::from_iter(v.into_iter());
        let b = create_bitvector(vec![0,0,1,1]);

        // println!("full : {:?}", b);
        let mut my = FibonacciDecoder {
            buffer: b.as_bitslice(),
            current_pos: 0,
            shifted_by_one: false,
        };

        assert_eq!(my.next(), Some(3));
        assert_eq!(my.next(), None);
    }

    #[test]
    fn test_myfib_decoder_consecutive_ones() {
        let b = create_bitvector(vec![0,0,1,1,1,1]);

        println!("full : {:?}", b);
        let mut my = FibonacciDecoder {
            buffer: b.as_bitslice(),
            current_pos: 0,
            shifted_by_one: false,
        };

        assert_eq!(my.next(), Some(3));
        assert_eq!(my.next(), Some(1));
        assert_eq!(my.next(), None);
    }

    #[test]
    fn test_myfib_decoder_nothing() {
        let b = create_bitvector(vec![0,0,1,0,1,0,1]);

        let mut my = FibonacciDecoder {
            buffer: &b,
            current_pos: 0,
            shifted_by_one: false,
        };
        assert_eq!(my.next(), None);

        // shift
        let mut my = FibonacciDecoder {
            buffer: &b,
            current_pos: 0,
            shifted_by_one: true,
        };
        assert_eq!(my.next(), None);
    }
    #[test]
    fn test_myfib_decoder_shifted() {
        let b = create_bitvector(vec![0,0,1,1,1,1]);

        // println!("full : {:?}", b);
        let mut my = FibonacciDecoder {
            buffer: &b,
            current_pos: 0,
            shifted_by_one: true,
        };

        assert_eq!(my.next(), Some(2));
        assert_eq!(my.next(), Some(0));
        assert_eq!(my.next(), None);
    }
}
