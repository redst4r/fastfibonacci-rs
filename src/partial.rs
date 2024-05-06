//! Decoding a fibonacci number in several steps.
//! Each step will create/update a Partial decoding result
//! and finally, once 11 is encountered will result in a decoded number

// use std::marker::PhantomData;

use crate::{fastutils::fibonacci_left_shift, utils::FIB64};
/*
enum DecState {
    Partial {
        num: u64,
        i_fibo: usize,
        last_bit: u64
    },
    Complete(u64)
}
impl DecState {
    pub fn update(mut self, bit: u64) -> Self {
        match self {
            DecState::Partial { mut num, mut i_fibo, last_bit } => {
                num += bit * FIB64[i_fibo];  // todo: i_fibo cant be bigger than 64!!
                i_fibo += 1;
                if last_bit + bit >= 2 {
                    DecState::Complete(num)
                } else {
                    DecState::Partial {
                        num,
                        i_fibo,
                        last_bit: bit
                    }
                }
            },
            DecState::Complete(_) => todo!(),
        }
    }
}

#[test]
fn test_de() {
    let mut s = DecState::Partial{num:0, i_fibo:0, last_bit: 0};
    let bits = vec![0,0,0,1, 0, 1, 1];

    for b in bits {
        match s.update(b) {
            DecState::Partial { num, i_fibo, last_bit } => {
                s = DecState::Partial { num, i_fibo, last_bit }
            } ,
            DecState::Complete(x) => {
                println!("decoded {x}");

                break;
            },
        }
    }
}*/

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
	///
	pub fn new(num: u64, i_fibo: usize, last_bit: u64) -> Self {
		Self {num, i_fibo, last_bit}
	}

    ///
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
    /// consumes the old encoding to make sure we dont use it any more
    pub fn combine_partial(&mut self, p_old: Partial) {
        // the new num is: the old num + the new num (adjusted for the additional bits)
        let new_num = p_old.num + fibonacci_left_shift(self.num, p_old.i_fibo);
        let new_i = p_old.i_fibo + self.i_fibo;
        let new_last = self.last_bit;

        self.num = new_num;
        self.i_fibo = new_i;
        self.last_bit = new_last;    
    }


}
impl Default for Partial {
	fn default() -> Self {
		Self::new( 0, 0, 0 )
	}
}

#[test]
fn test_de_partial() {
    let mut s:Partial = Default::default();
    let bits = vec![0,1,0,1, 1, 1, 1];

    let mut res=0;
    for b in bits {
        println!("{}", b);
        match s.update(b) {
            DecResult::Incomplete => {},
            DecResult::Complete(number) =>{
                println!("{}", number);
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


    p2.combine_partial(p_old);

    // combined those would be 1+5+34+233 = 273
    // todo the last bit of p1 and the first bit of p2 should never both the 1!!
    // let added = combine_partial(p_old, p2);
    assert_eq!(
        p2,
        Partial::new(273, 12, 1)
    )
}