//! Some older, slower code for fibonacci encoding.
//! mostly educational
use itertools::izip;

use crate::utils::FIB64;
use crate::{MyBitVector, MyBitSlice};
/// Fibonacci encoding of a single integer
///
/// # Example:
/// ```rust
/// # use fastfibonacci::fibonacci_old::encode;
/// let enc = encode(1);  // a BitVec
/// assert_eq!(enc.iter().collect::<Vec<_>>(), vec![true, true]);
/// ```
pub fn encode(mut n: u64) -> MyBitVector {
    assert!(n > 0, "n must be positive");
    assert!(n < FIB64[FIB64.len() - 1], "n must be smaller than max fib");

    let mut i = FIB64.len() - 1;
    let mut indices = Vec::new(); //indices of the bits that are set! will be sortet highest-lowest
    while n > 0 {
        if FIB64[i] <= n {
            indices.push(i);
            n -= FIB64[i];
        }
        if n == 0 {
            //otherwise the i-1 might cause underflow
            break;
        }
        i -= 1;
    }
    let max_ix = indices[0];

    let mut bits = MyBitVector::repeat(false, max_ix + 1);

    // set all recoded bits
    for i in indices {
        bits.set(i, true);
    }
    // add a final 1 to get the terminator
    bits.push(true);

    bits
}

/// Encode multiple integers into a bitvector via Fibonacci Encoding
pub fn fib_enc_multiple(data: &[u64]) -> MyBitVector {
    let mut acc = MyBitVector::new();

    for &x in data {
        let mut b = encode(x);
        acc.append(&mut b);
    }
    acc
}

/// convert a bitslice holding a single fibbonacci encoding into the numerical representation.
/// Essentially assumes that the bitslice ends with ....11 and has no other occurance of 11
fn bitslice_to_fibonacci(b: &MyBitSlice) -> u64 {
    // omits the initial 1, i.e.
    // fib = [1,2,3,5,...]
    // let fib: Vec<_> = iterative_fibonacci().take(b.len() - 1).collect(); // shorten by one as we omit the final bit
    // println!("{:?}", fib);
    // b.ends_with(&[true, true].into());
    if b.len() > 64 {
        panic!("fib-codes cant be longer than 64bit, something is wrong!");
    }
    // TODO make sure its a proper fib-encoding (no 11 except the end)
    let mut sum = 0;
    for (bit, f) in izip!(&b[..b.len() - 1], FIB64) {
        if *bit {
            sum += f;
        }
    }
    sum
}

///
fn bitslice_to_fibonacci3(b: &MyBitSlice) -> u64 {
    // omits the initial 1, i.e.
    // fib = [1,2,3,5,...]
    // let fib: Vec<_> = iterative_fibonacci().take(b.len() - 1).collect(); // shorten by one as we omit the final bit
    // println!("{:?}", fib);
    // b.ends_with(&[true, true].into());
    if b.len() > 64 {
        panic!("fib-codes cant be longer than 64bit, something is wrong!");
    }
    // TODO make sure its a proper fib-encoding (no 11 except the end)
    let mut sum = 0;
    // for (bit, f) in izip!(&b[..b.len()-1], FIB64) {
    for i in 0..b.len() - 1 {
        sum += FIB64[i] * (b[i] as u64);
    }
    sum
}

///
fn bitslice_to_fibonacci2(b: &MyBitSlice) -> u64 {
    // omits the initial 1, i.e.
    // fib = [1,2,3,5,...]
    // let fib: Vec<_> = iterative_fibonacci().take(b.len() - 1).collect(); // shorten by one as we omit the final bit
    // println!("{:?}", fib);
    // b.ends_with(&[true, true].into());
    if b.len() > 64 {
        panic!("fib-codes cant be longer than 64bit, something is wrong!");
    }
    // TODO make sure its a proper fib-encoding (no 11 except the end)
    let mut sum = 0;
    for ix in b[..b.len() - 1].iter_ones() {
        sum += FIB64[ix];
    }
    sum
}

///
fn bitslice_to_fibonacci4(b: &MyBitSlice) -> u64 {
    // omits the initial 1, i.e.
    // fib = [1,2,3,5,...]
    // let fib: Vec<_> = iterative_fibonacci().take(b.len() - 1).collect(); // shorten by one as we omit the final bit
    // println!("{:?}", fib);
    // b.ends_with(&[true, true].into());
    if b.len() > 64 {
        panic!("fib-codes cant be longer than 64bit, something is wrong!");
    }
    // TODO make sure its a proper fib-encoding (no 11 except the end)
    // let mut sum = 0;
    let sum = b[..b.len() - 1]
        .iter()
        .by_vals()
        .enumerate()
        .filter_map(|(ix, bit)| if bit { Some(FIB64[ix]) } else { None })
        .sum();
    sum
}


#[cfg(test)]
mod test {
    use bitvec::{bits, order::Msb0, vec::BitVec};

    use super::encode;
    use crate::{fibonacci_old::{fib_enc_multiple, bitslice_to_fibonacci}, MyBitVector};

    #[test]
    fn test_fib_encode_5() {
        assert_eq!(
            encode(5).iter().collect::<Vec<_>>(),
            vec![false, false, false, true, true]
        );
    }
    #[test]
    fn test_fib_encode_1() {
        assert_eq!(encode(1).iter().collect::<Vec<_>>(), vec![true, true]);
    }
    #[test]
    fn test_fib_encode_14() {
        assert_eq!(
            encode(14).iter().collect::<Vec<_>>(),
            vec![true, false, false, false, false, true, true]
        );
    }

    #[test]
    fn test_fib_encode_mutiple() {
        let enc = fib_enc_multiple(&vec![1, 14]);
        assert_eq!(
            enc.iter().collect::<Vec<_>>(),
            vec![true, true, true, false, false, false, false, true, true]
        );
    }

    #[test]
    #[should_panic(expected = "n must be positive")]
    fn test_fib_encode_0() {
        encode(0);
    }
    #[test]
    #[should_panic(expected = "n must be smaller than max fib")]
    fn test_fib_encode_u64max() {
        encode(u64::MAX);
    }


    #[test]
    fn test_bitslice_to_fibonacci() {
        let b = bits![u8, Msb0; 1, 1];

        assert_eq!(bitslice_to_fibonacci(b), 1);

        let b = bits![u8, Msb0; 0, 1, 1];

        assert_eq!(bitslice_to_fibonacci(&b), 2);
        let b = bits![u8, Msb0; 0,0,1, 1];

        assert_eq!(bitslice_to_fibonacci(&b), 3);

        let b = bits![u8, Msb0; 1,0, 1, 1];
        assert_eq!(bitslice_to_fibonacci(&b), 4);

        let b = bits![u8, Msb0; 1,0,0,0,0,1,1];

        assert_eq!(bitslice_to_fibonacci(&b), 14);

        let b = bits![u8, Msb0; 1,0,1,0,0,1,1];
        assert_eq!(bitslice_to_fibonacci(&b), 17);
    }

    #[test]
    fn test_max_decode() {
        let mut v: Vec<bool> = [0_u8; 64].iter().map(|x| *x == 1).collect();
        v[62] = true;
        v[63] = true;

        let b: MyBitVector = BitVec::from_iter(v.into_iter());
        assert_eq!(bitslice_to_fibonacci(&b), 10610209857723);
    }
}
