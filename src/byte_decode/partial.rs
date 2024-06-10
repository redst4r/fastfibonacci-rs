//! Decoding a fibonacci number in several steps.
//! Each step will create/update a Partial decoding result
//! and finally, once 11 is encountered will result in a decoded number
use crate::{fastutils::fibonacci_left_shift, utils::FIB64};

/// A Partial Fibonacci-decoding result:
/// The input stream finished before we could decode a complete integer.
/// This struct contains all information to continue the decoding of the current number
/// with another bitstream
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Partial {
    pub (crate) num: u64,
    pub (crate)i_fibo: usize,
    pub (crate)last_bit: u64
}

pub (crate) enum DecResult {
    Incomplete,
    Complete(u64)
}

impl Partial {
	/// A partial decoding, `num` is the number decoded so far, we're in `i_fibo` bits and `last_bit` is the last bit we saw.
	pub fn new(num: u64, i_fibo: usize, last_bit: u64) -> Self {
		Self {num, i_fibo, last_bit}
	}

    /// adding another bit to the decoding.
    /// Will either return a sucessfukl decoding (if we hit 11) or an updated partial decoding.
    pub (crate) fn update(&mut self, bit: u64) -> DecResult{
        if self.last_bit + bit >= 2 {
            DecResult::Complete(self.num)
        } else {
            self.num += bit * FIB64[self.i_fibo];  // todo: i_fibo cant be bigger than 64!!
            self.i_fibo += 1;
            self.last_bit = bit;
            DecResult::Incomplete
        }
    }

    /// adding a previous partial decoding to `self`
    /// modifies `self`
    pub fn combine_partial(&mut self, p_old: &Partial) {
        // the new num is: the old num + the new num (adjusted for the additional bits)
        let new_num = p_old.num + fibonacci_left_shift(self.num, p_old.i_fibo);
        // let new_i = p_old.i_fibo + self.i_fibo;
        let new_last = self.last_bit;

        self.num = new_num;
        // self.i_fibo = new_i;
        self.i_fibo += p_old.i_fibo;
        self.last_bit = new_last;    
    }

    /// checks if there's any leftover in the decoding, or just a bunch of zeros
    /// which could be considered padding
    pub fn is_clean(&self) -> bool {
        // i_fibo doesnt matter, it gets increase even for zeros
        self.last_bit == 0 && self.num == 0
    }
}

impl Default for Partial {
	fn default() -> Self {
		Self::new( 0, 0, 0 )
	}
}

#[inline]
// adding a partial decoding (from previous segment) to a fully decoded number (in the current segemnt)
pub (crate) fn number_plus_partial(x: u64, p: &Partial) -> u64{
    p.num + fibonacci_left_shift(x, p.i_fibo)
}

#[cfg(test)]
mod testing {
    use super::*;
    #[test]
    fn test_de_partial() {
        let mut s:Partial = Default::default();
        let bits = vec![0,1,0,1, 1, 1, 1];

        let mut res=0;
        for b in bits {
            // println!("{}", b);
            match s.update(b) {
                DecResult::Incomplete => {},
                DecResult::Complete(number) =>{
                    // println!("{}", number);
                    res = number;
                    break;
                },
            }
        }
        assert_eq!(7, res);
    }

    #[test]
    fn test_add_partial() {
        // 6 = 1001_fib
        let p_old = Partial::new(6, 4, 1);

        // 00010001_fib = 39
        let mut p2 = Partial::new(39, 8, 1);


        p2.combine_partial(&p_old);

        // combined those would be 1+5+34+233 = 273
        // todo the last bit of p1 and the first bit of p2 should never both the 1!!
        // let added = combine_partial(p_old, p2);
        assert_eq!(
            p2,
            Partial::new(273, 12, 1)
        )
    }
}