//!
use std::marker::PhantomData;
use funty::Integral;

use crate::byte_decode::{bare_metal_generic_single::DirtyGenericSingle,  partial::Partial};
use crate::fastutils::{fibonacci_left_shift, State};

/// Kind of a marker trait which we can use 
/// for our lookup table
trait StorageInteger {
    fn to_usize(&self) -> usize;
    fn nbits() -> usize;
}

impl StorageInteger for u8 {
    fn to_usize(&self) -> usize {
        *self as usize
     }
     
    fn nbits() -> usize {
        8
    }
}

impl StorageInteger for u16 {
    fn to_usize(&self) -> usize {
        *self as usize
     }
     
    fn nbits() -> usize {
        16
    }
}

fn padding<T:Integral>(x: T) -> T {
    if x > T::ZERO{
        x << x.leading_zeros()
    } else {
        T::ZERO
    }
}

///
pub struct LookupVecNew<T> {
    table_state0: Vec<(Vec<u64>, Partial)>,
    table_state1: Vec<(Vec<u64>, Partial)>,
    dummy: PhantomData<T>,
}
impl <T:Integral>LookupVecNew<T> {    /// Create a new Lookup table for fast fibonacci decoding using 16bit segments.
    /// This implementation uses a vec.
    pub fn new() -> Self {
        let segment_size = T::BITS as usize;

        let mut table_state0 = Vec::new();
        let mut table_state1 = Vec::new();
    
        for lastbit in [true, false]{
            let max = usize::pow(2, segment_size as u32);
            for s in 0..max {

                /* This whole conversion part is a bit hacky!! */
                // we need to convert to the segment tye: u8, u16, depdingn on how wide the segement
                let s_tmp: T = match s.try_into() {
                    Ok(i) => i,
                    Err(_) => panic!("cant convert segment to proper u8/u16.."),
                };
                // println!("integer {s_tmp}, binary {s_tmp:b}");
                
                // padding to the right
                // let t = padding(s_tmp);
                // println!("pad int {t}, binary {t:b}");
                let t = s_tmp;
                
                // println!("Unpad {s:b}");
                // println!("Pad   {t:b}");

                // let mut dd = Dirty64Single::new(t as u64);
                let mut dd = DirtyGenericSingle::new(t);
                let partial = Partial::new(0, 0, lastbit as u64); // it'll be overwritten by the match/err, just need to init here

                let (numbers, partial) = dd.decode_all_from_partial(partial);

                // insert result based on new state                 
                if lastbit {
                    table_state1.push((numbers, partial));
                }
                else{
                    table_state0.push((numbers, partial));
                }
            }
        }
        LookupVecNew { table_state0, table_state1, dummy: PhantomData}
    }
}

/// Fast Fibonacci decoding lookup table for u8/u16/... segment sizes.
/// Note: u32 technically possible, but the table GETS HUGE (2**32 entries)
/// and takes very long to generate.
pub trait LookupTableNew<T> {
    /// Given the state of the last decoding operation and the new segment, returns
    /// the (precomputed) new state and decoding result.
    fn lookup(&self, s: State, segment: T) -> (&[u64], &Partial);
}


impl <T:Integral> LookupTableNew<T> for LookupVecNew<T> {
    // fn lookup(&self, s: State, segment: T) -> (Vec<u64>, Partial) {
    fn lookup(&self, s: State, segment: T) -> (&[u64], &Partial) {
            
        // we're indexing into the vec, this needs to be usize
        let idx:  usize = match segment.try_into(){
            Ok(i) => i,
            Err(_) => panic!("couldnt convert vec index to usize"),
        };

        let (numbers, partial) = match s {
            State(0) => self.table_state0.get(idx).unwrap(),
            State(1) => self.table_state1.get(idx).unwrap(),
            // State(0) => &self.table_state0[segment as usize],
            // State(1) => &self.table_state1[segment as usize],            
            State(_) => panic!("yyy")
        };
        (numbers, partial)
    }
}

#[cfg(test)]
mod testing_lookups {
    use bitvec::prelude::*;
    use crate::utils::create_bitvector;

    use super::*;
    // use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_vec8_lookup() {
        // u8
        let t: LookupVecNew<u8> = LookupVecNew::new();
        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1]).load_be::<u8>();

        assert_eq!(
            t.lookup(State(0), i), 
            (vec![4].as_slice(), &Partial { num:7, i_fibo: 4, last_bit: 1})
        );

        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1]).load_be::<u8>();
        assert_eq!(
            t.lookup(State(1), i), 
            (vec![0,2].as_slice(), &Partial { num:7, i_fibo: 4, last_bit: 1})
        );   

        let i = create_bitvector(vec![ 0,1,1,1,0,0,1,0]).load_be::<u8>();
        assert_eq!(
            t.lookup(State(1), i), 
            (vec![2].as_slice(), &Partial { num:6, i_fibo: 5, last_bit: 0})
        );   
        assert_eq!(
            t.lookup(State(0), i), 
            (vec![2].as_slice(), &Partial { num:6, i_fibo: 5, last_bit: 0})
        ); 
    }
}


/// Fast Fibonacci decoding of the entire bitstream using the precomputed lookup table.
/// 
/// Fibonacci decoding cannot handle zeros, and often during the encoding, every value is incremented by one (to encode zero as 1).
/// If `shifted_by_one` is `true`, we decrement each decoded value by 1, assuming that the encoder artificially incremented each value before encoding. 
pub fn fast_decode_new<T:Integral>(stream: &[T], shifted_by_one: bool, table: &impl LookupTableNew<T>) -> Vec<u64> {

    let mut partial = Partial::new(0, 0, 0);
    let mut decoded_numbers= Vec::new();

    for &segment_int in stream {  // just go over the input bytes (or u16)

        // println!("decoding integer {segment_int}, binary {segment_int:b}");

        // need to pad
        // actually dont!
        // let segment_int_pad = padding(segment_int);
        let segment_int_pad = segment_int;

        let (numbers, p) = table.lookup(State(partial.last_bit as usize), segment_int_pad);
        // println!("numbers {numbers:?}, partial {p:?}");

        // now, we need to properly decode those numbers:
        // if the previous segment left over something (see partial)
        // we need to "add" this to numbers[0]
        // if not, we need to merge p (the new partial decode from stream[i]) and partial (the old partial decode from stream(i-1))
        if !numbers.is_empty() {
            // println!("Combining {numbers:?} with {partial:?}");
            // absorb `partial` (the old decoding) into the number
            // and keep the new decoding status as is
            let new_x = number_plus_partial(numbers[0], &partial);
            // println!("newx {new_x}");
            decoded_numbers.push(new_x);

            decoded_numbers.extend(&numbers[1..]);


            // numbers[0] = new_x;
            partial = p.clone();
        } else {
            // "add" p and partial; ORDER is important
            // partial = combine_partial(partial, p)
            let mut newp = p.clone();
            newp.combine_partial(partial);
            partial = newp;
        }
    }

    // TODO: check that partial is empy!

    if shifted_by_one{
        decoded_numbers.iter().map(|x| x - 1).collect::<Vec<u64>>()
    } else {
        decoded_numbers
    }
}

// adding a partial decoding (from previous segment) to a fully decoded number (in the current segemnt)
fn number_plus_partial(x: u64, p: &Partial) -> u64{
    p.num + fibonacci_left_shift(x, p.i_fibo)
}

#[cfg(test)]
mod test {
    use crate::utils::{bits_to_fibonacci_generic_array, create_bitvector, random_fibonacci_stream};

    use super::*;
    #[test]
    fn test_fast_decode() {

        // the exampel from the paper, Fig 9.4
        let bits = create_bitvector(vec![ 
            1,0,1,1,0,1,0,1,
            1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0]).to_bitvec();

        let x_u8 = bits_to_fibonacci_generic_array::<u8>(&bits);
        let x_u16 = bits_to_fibonacci_generic_array::<u16>(&bits);

        let t: LookupVecNew<u8> = LookupVecNew::new();
        let r = fast_decode_new(&x_u8,false, &t);
        assert_eq!(r, vec![4,7, 86]);

        let t: LookupVecNew<u16> = LookupVecNew::new();
        let r = fast_decode_new(&x_u16,false, &t);
        assert_eq!(r, vec![4,7, 86]);
    }

    #[test]
    fn test_correctness_fast_decode_u8() {
        use crate::bit_decode::fibonacci::FibonacciDecoder;
        let bits = random_fibonacci_stream(100000, 1, 1000, 123455);

        let x_u8 = bits_to_fibonacci_generic_array::<u8>(&bits);
        let x_u16 = bits_to_fibonacci_generic_array::<u16>(&bits);


        // ground thruth
        let dec = FibonacciDecoder::new(&bits, false);
        let x1: Vec<_> = dec.collect();

        let t: LookupVecNew<u8> = LookupVecNew::new();
        let x2 = fast_decode_new(&x_u8,false, &t);        
        assert_eq!(x1, x2);


        let t: LookupVecNew<u16> = LookupVecNew::new();
        let x2 = fast_decode_new(&x_u16,false, &t);        
        assert_eq!(x1, x2);
    }
}