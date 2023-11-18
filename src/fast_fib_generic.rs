//!
//! 
//! 
use std::marker::PhantomData;
use bitvec::{view::BitView, field::BitField, store::BitStore};
use funty::Integral;
use crate::fibonacci_fast::{decode_with_remainder, DecodingResult, State, DecodingState, FFBitvec, FFBitorder};

/// Fast Fibonacci decoding lookup table for u8/u16 segment sizes
/// Note: u32 technically possible, but the table GETS HUGE (2**32 entries)
/// and takes very long to generate

pub trait LookupTable<T> {
    /// given the state of the last decoding operation and the new segment, returns
    /// the (precomputed) new state and decoding result
    fn lookup(&self, s: State, segment: T) -> (State, &DecodingResult);
}
/// Vector based lookup table for u8/u16
pub struct LookupVec<T> {
    table_state0: Vec<(State, DecodingResult)>,
    table_state1: Vec<(State, DecodingResult)>,
    dummy: PhantomData<T>,
}
impl <T:Integral+BitStore>LookupVec<T> {
    /// create a new Lookup table for fast fibonacci decoding using 16bit segments
    /// This implementation uses a vec
    pub fn new() -> Self {
        let segment_size = T::BITS as usize;

        let mut table_state0 = Vec::new();
        let mut table_state1 = Vec::new();
    
        for lastbit in [true, false]{
            let max = usize::pow(2, segment_size as u32);
            for s in 0..max {

                // we need to convert to the segment tye: u8, u16, depdingn on how wide the segement
                let t: T = match s.try_into() {
                    Ok(i) => i,
                    Err(_) => panic!("cant convert segment to proper u8/u16.."),
                };
                let bitstream = t.view_bits::<FFBitorder>().to_owned();
                assert_eq!(bitstream.len(), segment_size);
                // determining the new state is a bit more tricky than just looking
                // at the last bit of the segment:
                // 1. if the segment terminated with (11), this resets the state to 0
                //     xxxxxx11|1
                //     otherwise this would immediately terminate in [0]. But really the last bit
                //     has been used up in the terminator
                // 2. otherwise, we still have to be carefull:
                //     00000111|10000000
                //          OR
                //     000(11)(11)1|10000000
                //    Even though the last bits are 11, this is NOT a terminator
                //    and the next state indeed is 1
                //
                // The easiest way is to just see what comes back from the decoding:
                // We get the number of bits after the last terminator and can hence
                // pull out all the bits in questions

                let r = decode_with_remainder(&bitstream, lastbit);
                // we need to know the bits behind the last terminator
                let trailing_bits= &bitstream[bitstream.len()-r.lu..];
                let newstate = if trailing_bits.is_empty() {
                    // we ended with a temrinator:  xxxxxx11|yyy
                    // resets the state to 0
                    State(0)
                } else {
                    let final_bit = trailing_bits[trailing_bits.len()-1];
                    if final_bit { State(1)} else {State(0)}
                };

                // insert result based on new state                 
                if lastbit {
                    table_state1.push((newstate, r));
                }
                else{
                    table_state0.push((newstate, r));
                }
            }
        }
        LookupVec { table_state0, table_state1, dummy: PhantomData}
    }
}

impl <T:Integral> LookupTable<T> for LookupVec<T> {
    fn lookup(&self, s: State, segment: T) -> (State, &DecodingResult) {
            
        // we're indexing into the vec, this needs to be usize
        let idx:  usize = match segment.try_into(){
            Ok(i) => i,
            Err(_) => panic!("couldnt convert vec index to usize"),
        };

        let (newstate, result) = match s {
            State(0) => self.table_state0.get(idx).unwrap(),
            State(1) => self.table_state1.get(idx).unwrap(),
            // State(0) => &self.table_state0[segment as usize],
            // State(1) => &self.table_state1[segment as usize],            
            State(_) => panic!("yyy")
        };
        (*newstate, result)
    }
}

/// -> each segment can be represented by a number, which solves the problem of slow hashmap access
pub fn fast_decode_generic<T:Integral>(stream: FFBitvec, table: &impl LookupTable<T>) -> Vec<u64> {

    // println!("Total stream {}", bitstream_to_string(&stream));
    let segment_size = T::BITS as usize;
    let mut decoding_state = DecodingState::new();

    // let mut n_chunks = stream.len() / segment_size;
    // if stream.len() % segment_size > 0 {
    //     n_chunks+= 1;
    // } 

    let mut state = State(0);
    // for i in 0..n_chunks{
    for segment in stream.chunks(segment_size) {
        // get a segment
        // let start = i*segment_size;
        // let end = cmp::min((i+1)*segment_size, stream.len());
        // let segment = &stream[start..end];

        // NOTE: WE NEED TO PAD segments chunks that are smaller than segment_size ON THE RIGHT!!
        // this here pads depedingin on BitOrder: Lsb: right padding; Msb: left padding
        let mut segment_int = segment.load_be::<T>();

        // to be generic over bitorder, we better do the padding ourselves!
        // turns out we can just do that with bitshifts on the integer
        // Msb:
        // pad   | 
        // 000000|1001101100
        // shift by 6
        // 1001101100|000000
        // Lsb
        // 1001101100|000000
        // now need to do anything!
        if segment.len() < segment_size {
            segment_int <<= segment_size - segment.len();
        }

        let (newstate, result) = table.lookup(state, segment_int);

        // println!("Segment: {}, SegmentInt {}", segment, segment_int);
        // println!("Decoded state: {:?}, result {:?}", newstate, result);

        state = newstate;
        // update the current decoding state:
        // add completely decoded numbers, deal with partially decoded numbers        
        decoding_state.update(result);
        // println!("Updated state: {:?}", decoding_state);

    }
    decoding_state.decoded_numbers
}

#[cfg(test)]
mod testing_lookups {
    use bitvec::prelude::*;
    use super::*;
    // use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_vec8_lookup() {

        // u8
        let t: LookupVec<u8> = LookupVec::new();
        let i = bits![u8, FFBitorder; 1,0,1,1,0,1,0,1].load_be::<u8>();

        assert_eq!(
            t.lookup(State(0), i), 
            (State(1), &DecodingResult {numbers: vec![4], u:7, lu: 4, number_end_in_segment: vec![3]})
        );

        let i = bits![u8, FFBitorder; 1,0,1,1,0,1,0,1].load_be::<u8>();
        assert_eq!(
            t.lookup(State(1), i), 
            (State(1), &DecodingResult {numbers: vec![0, 2], u:7, lu: 4, number_end_in_segment: vec![0, 3]})
        );   
    }
    #[test]
    fn test_vec16_lookup() {
        // u16
        let t: LookupVec<u16> = LookupVec::new();
        let i = bits![u8, FFBitorder; 1,0,1,1,0,1,0,1, 0,0,1,1,0,0,0,1].load_be::<u16>();

        assert_eq!(
            t.lookup(State(0), i), 
            (State(1), &DecodingResult {numbers: vec![4, 28], u:5, lu: 4, number_end_in_segment: vec![3, 11]})
        );

        let i = bits![u8, FFBitorder; 1,0,1,1,0,1,0,1, 0,0,1,1,0,0,0,1].load_be::<u16>();
        assert_eq!(
            t.lookup(State(1), i), 
            (State(1), &DecodingResult {numbers: vec![0, 2, 28], u:5, lu: 4, number_end_in_segment: vec![0,3,11]})
        );  
    }

    #[test]
    fn test_decode_vec() {
        let t: LookupVec<u8> = LookupVec::new();
        let bits = bits![u8, FFBitorder; 1,0,1,1,0,1,0,1,   0, 1, 0, 0, 0, 1, 1, 0].to_bitvec();

        assert_eq!(
            fast_decode_generic(bits, &t),
             vec![4, 109]
        );  
    }
    
}

#[cfg(test)]
mod testing_fast_decode {
    use bitvec::prelude::*;
    use super::*;
    // use pretty_assertions::assert_eq;
    
    #[test]
    fn test_fast_decode_correct_padding() {
        // if the chunk is smaller than the segmentsize, it becomes important how we pad it back to 
        // sgementsize
        // the exampel from the paper, Fig 9.4
        let bits = bits![u8, FFBitorder; 
            1,0,1,1].to_bitvec();

        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);
        assert_eq!(r, vec![4]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);
        assert_eq!(r, vec![4]);

        // let t: LookupVec<u32> = LookupVec::new();
        // let r = fast_decode_generic(bits.clone(), &t);
        // assert_eq!(r, vec![4]);        
    }

    #[test]
    fn test_fast_decode() {

        // the exampel from the paper, Fig 9.4
        let bits = bits![u8, FFBitorder; 
            1,0,1,1,0,1,0,1,
            1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0].to_bitvec();

        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);
        assert_eq!(r, vec![4,7, 86]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);
        assert_eq!(r, vec![4,7, 86]);

        // let t: LookupVec<u32> = LookupVec::new();
        // let r = fast_decode_generic(bits.clone(), &t);
        // assert_eq!(r, vec![4,7, 86]);
    }

    #[test]
    fn test_fast_decode_111_at_segment_border() {
        // edge case when the delimitator is algined with the segment and the next segment starts with 1
        // make sure to no double count 
        let bits = bits![u8, FFBitorder; 0,0,0,0,0,0,1,1,1,0,0,0,0,0,1,1].to_bitvec();
        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);        
        assert_eq!(r, vec![21, 22]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);        
        assert_eq!(r, vec![21, 22]); 

        // let t: LookupVec<u32> = LookupVec::new();
        // let r = fast_decode_generic(bits.clone(), &t);        
        // assert_eq!(r, vec![21, 22]);         
    }
    #[test]
    fn test_fast_decode_special_case() {
        // edge case when theres a bunch of 1111 at the end of the segment
        // we need to make sure that we dervie the new state correctly

        let bits = bits![u8, FFBitorder; 
            0,1,1,1,0,1,1,1,
            1].to_bitvec();
        let expected = vec![2, 4, 1];
        
        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);        
        assert_eq!(r, expected);

        // fr the u16, we need a much longer segment
        let bits = bits![u8, FFBitorder; 
            1,1,1,1,1,1,1,1,
            0,1,1,1,0,1,1,1,
            1].to_bitvec();
        let expected = vec![1,1,1,1, 2, 4, 1];

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode_generic(bits.clone(), &t);        
        assert_eq!(r, expected);
    }

    #[test]
    fn test_correctness_fast_decode_u8() {
        use crate::fibonacci::FibonacciDecoder;
        use crate::fib_utils::random_fibonacci_stream;
        let b = random_fibonacci_stream(100000, 1, 1000);
        // let b = dummy_encode(vec![64, 11, 88]);
        // make a copy for fast decoder
        let mut b_fast: BitVec<u8, FFBitorder> = BitVec::new();
        for bit in b.iter().by_vals() {
            b_fast.push(bit);
        }
        let dec = FibonacciDecoder::new(&b, false);
        let x1: Vec<_> = dec.collect();

        let t: LookupVec<u8> = LookupVec::new();
        let x2 = fast_decode_generic(b_fast.clone(), &t);        
        assert_eq!(x1, x2);

        let t: LookupVec<u16> = LookupVec::new();
        let x2 = fast_decode_generic(b_fast.clone(), &t);        
        assert_eq!(x1, x2);

        // let t: LookupVec<u32> = LookupVec::new();
        // let x2 = fast_decode_generic(b_fast.clone(), &t);        
        // assert_eq!(x1, x2);
    }

    // #[test]
    #[allow(dead_code)]
    fn test_fast_speed() {
        use crate::fib_utils::random_fibonacci_stream;

        let b = random_fibonacci_stream(10_000_000, 100000, 1000000);
        // make a copy for fast decoder
        let mut b_fast: BitVec<u8, FFBitorder> = BitVec::new();
        for bit in b.iter().by_vals() {
            b_fast.push(bit);
        }

        let t: LookupVec<u8> = LookupVec::new();
        let x2 = fast_decode_generic(b_fast.clone(), &t);   

        println!("{}", x2.iter().sum::<u64>());

        let t: LookupVec<u16> = LookupVec::new();
        let x2 = fast_decode_generic(b_fast.clone(), &t);   
        println!("{}", x2.iter().sum::<u64>())    ;

        // let t: LookupVec<u32> = LookupVec::new();
        // let x2 = fast_decode_generic(b_fast.clone(), &t);   
        // println!("{}", x2.iter().sum::<u64>())    ;
    }
}
