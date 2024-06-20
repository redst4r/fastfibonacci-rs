//! Fast Fibonacci En/De-coding Algorithm,
//! see this [paper](https://www.researchgate.net/publication/220827231_Fast_Fibonacci_Encoding_Algorithm) for encoding and 
//! this [paper](https://www.semanticscholar.org/paper/Fast-data-Encoding-and-Deconding-Algorithms-Walder/4fbae5afc34dd32e7527fe4b1a1bd19e68794e3d) for the decoding.
//!
//! # Decoding
//! Instead of decoding bit by bit, we do larger segments of bits, where
//! we precomputed their decoded representation already in a lookup table ([`LookupVec`], generic over u8, u16, depending on the desired chunksize).

//! The tricky part: A segment might have a encoded number, but also parts of the next encoded number:
//! ```bash,no_run  
//! segment1|segment 2
//! 00001100|11000011
//!       ----- Remainder
//! ```
//!
//! ## Example
//! ```rust
//! use fastfibonacci::bit_decode::fast::{fast_decode, LookupVec, get_u8_decoder,get_u16_decoder};
//! use bitvec::prelude as bv;
//! let bits = bv::bits![u8, bv::Msb0;
//!     1,0,1,1,0,1,0,1,
//!     1,0,1,0,0,1,0,1,
//!     0,1,1,1,0,0,1,0].to_bitvec();
//! 
//! // using a u8 lookup table
//! let table8: LookupVec<u8> = LookupVec::new();
//! let r = fast_decode(&bits, false, &table8);
//! assert_eq!(r, vec![4,7, 86]);
//!
//! // using a u16 table
//! let table16: LookupVec<u16> = LookupVec::new();
//! let r = fast_decode(&bits, false, &table16);
//! assert_eq!(r, vec![4,7, 86]);
//! 
//! // Getting an iterator over the decoded values
//! let dec8 = get_u8_decoder(&bits, false);
//! assert_eq!(dec8.collect::<Vec<_>>(), vec![4,7, 86]);
//! 
//! let dec16 = get_u16_decoder(&bits, false);
//! assert_eq!(dec16.collect::<Vec<_>>(), vec![4,7, 86]);
//! ```
//! 
//! ## Lookup tables
//! Using [`LookupVec<u8>`] will process the bitstream in 8-bit chunks, [`LookupVec<u16>`] will do it in 16-bit chunks.
//! Theoretically, bigger chunks should be faster, but the lookup-table becomes much larger (2^16 vs 2^8).
//!
//! The logic of those lookup tables is a bit complicated:
//! A chunk/segment might have a encoded number, but also parts of the next encoded number:
//! ```bash,no_run  
//! segment1|segment 2
//! 00001100|11000011
//!       ----- Remainder
//! ```
//! We need to keep track of 
//! i) the decoded numbers so far, 
//! ii) the remaining bits of the previous buffer, 
//! iii) the last bit of the previous buffer
//! This is done in [`crate::fastutils::DecodingResult`]
//! 
//! Turns out that the implementation details are pretty important.
//! Implementing a simple lookup table as a `HashMap<Segment, ...>` is actually **slower** than simple bit-by-bit decoding.
//! One has to exploit the fact that a segment can be represented by an integer,
//! and store the results in a vec, indexed by the segment. 
//! That is, we create a **Lookup table** (see [`LookupVec`] ) which we can quickly query for incoming segments.
//!

use std::collections::VecDeque;
use std::marker::PhantomData;
use std::cmp;
use once_cell::sync::Lazy;
use bitvec::{view::BitView, field::BitField, store::BitStore};
use funty::Integral;
use crate::bit_decode::{FbDec, MyBitOrder, MyBitSlice};
use crate::fastutils::{DecodingResult, State, DecodingState, decode_with_remainder};

/// Fast Fibonacci decoding lookup table for u8/u16/... segment sizes.
/// Note: u32 technically possible, but the table GETS HUGE (2**32 entries)
/// and takes very long to generate.
pub trait LookupTable<T> {
    /// Given the state of the last decoding operation and the new segment, returns
    /// the (precomputed) new state and decoding result.
    fn lookup(&self, s: State, segment: T) -> (State, &DecodingResult);
}

/// Vector based lookup table for u8/u16 segments.
pub struct LookupVec<T> {
    table_state0: Vec<(State, DecodingResult)>,
    table_state1: Vec<(State, DecodingResult)>,
    dummy: PhantomData<T>,
}
impl <T:Integral+BitStore>LookupVec<T> {
    /// Create a new Lookup table for fast fibonacci decoding using 16bit segments.
    /// This implementation uses a vec.
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
                let bitstream = t.view_bits::<MyBitOrder>().to_owned();
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
                    State(false)
                } else {
                    let final_bit = trailing_bits[trailing_bits.len()-1];
                    if final_bit { State(true)} else {State(false)}
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
            State(false) => self.table_state0.get(idx).unwrap(),
            State(true) => self.table_state1.get(idx).unwrap(),
            // State(0) => &self.table_state0[segment as usize],
            // State(1) => &self.table_state1[segment as usize],            
        };
        (*newstate, result)
    }
}

/// Fast Fibonacci decoding of the entire bitstream using the precomputed lookup table.
/// 
/// Fibonacci decoding cannot handle zeros, and often during the encoding, every value is incremented by one (to encode zero as 1).
/// If `shifted_by_one` is `true`, we decrement each decoded value by 1, assuming that the encoder artificially incremented each value before encoding. 
pub fn fast_decode<T:Integral>(stream: &MyBitSlice, shifted_by_one: bool, table: &impl LookupTable<T>) -> Vec<u64> {

    // println!("Total stream {}", bitstream_to_string(&stream));
    let segment_size = T::BITS as usize;
    let mut decoding_state = DecodingState::new();

    // let mut n_chunks = stream.len() / segment_size;
    // if stream.len() % segment_size > 0 {
    //     n_chunks+= 1;
    // } 

    let mut state = State(false);
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

    if shifted_by_one{
        decoding_state.decoded_numbers.iter().map(|x| x - 1).collect::<Vec<u64>>()
    } else {
        decoding_state.decoded_numbers
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
        let t: LookupVec<u8> = LookupVec::new();
        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1]).load_be::<u8>();

        assert_eq!(
            t.lookup(State(false), i), 
            (State(true), &DecodingResult {numbers: vec![4], u:7, lu: 4, number_end_in_segment: vec![3]})
        );

        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1]).load_be::<u8>();
        assert_eq!(
            t.lookup(State(true), i), 
            (State(true), &DecodingResult {numbers: vec![0, 2], u:7, lu: 4, number_end_in_segment: vec![0, 3]})
        );   
    }
    #[test]
    fn test_vec16_lookup() {
        // u16
        let t: LookupVec<u16> = LookupVec::new();
        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1, 0,0,1,1,0,0,0,1]).load_be::<u16>();

        assert_eq!(
            t.lookup(State(false), i), 
            (State(true), &DecodingResult {numbers: vec![4, 28], u:5, lu: 4, number_end_in_segment: vec![3, 11]})
        );

        let i = create_bitvector(vec![ 1,0,1,1,0,1,0,1, 0,0,1,1,0,0,0,1]).load_be::<u16>();
        assert_eq!(
            t.lookup(State(true), i), 
            (State(true), &DecodingResult {numbers: vec![0, 2, 28], u:5, lu: 4, number_end_in_segment: vec![0,3,11]})
        );  
    }

    #[test]
    fn test_decode_vec() {
        let t: LookupVec<u8> = LookupVec::new();
        let bits = create_bitvector(vec![1,0,1,1,0,1,0,1,   0, 1, 0, 0, 0, 1, 1, 0]);

        assert_eq!(
            fast_decode(&bits, false, &t),
             vec![4, 109]
        );  
    }
}

#[cfg(test)]
mod testing_fast_decode {
    use bitvec::prelude::*;
    use super::*;
    use crate::{bit_decode::MyBitVector, utils::{create_bitvector, random_fibonacci_stream}};

    #[test]
    fn test_fast_decode_correct_padding() {
        // if the chunk is smaller than the segmentsize, it becomes important how we pad it back to 
        // sgementsize
        // the exampel from the paper, Fig 9.4
        let bits = create_bitvector(vec![ 
            1,0,1,1]).to_bitvec();

        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode(&bits, false, &t);
        assert_eq!(r, vec![4]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);
        assert_eq!(r, vec![4]);      
    }

    #[test]
    fn test_fast_decode() {

        // the exampel from the paper, Fig 9.4
        let bits = create_bitvector(vec![ 
            1,0,1,1,0,1,0,1,
            1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0]).to_bitvec();

        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);
        assert_eq!(r, vec![4,7, 86]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);
        assert_eq!(r, vec![4,7, 86]);
    }

    #[test]
    fn test_fast_decode_shift() {

        let bits = create_bitvector(vec![ 
            1,1,   // 0
            0,1,1, // 1
            0,0,1,1// 2
        ]).to_bitvec();

        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode(&bits, true, &t);
        assert_eq!(r, vec![0, 1, 2]);
    }

    #[test]
    fn test_fast_decode_111_at_segment_border() {
        // edge case when the delimitator is algined with the segment and the next segment starts with 1
        // make sure to no double count 
        let bits = create_bitvector(vec![ 0,0,0,0,0,0,1,1,1,0,0,0,0,0,1,1]).to_bitvec();
        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);        
        assert_eq!(r, vec![21, 22]);

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);        
        assert_eq!(r, vec![21, 22]);     
    }
    #[test]
    fn test_fast_decode_special_case() {
        // edge case when theres a bunch of 1111 at the end of the segment
        // we need to make sure that we dervie the new state correctly

        let bits = create_bitvector(vec![ 
            0,1,1,1,0,1,1,1,
            1]).to_bitvec();
        let expected = vec![2, 4, 1];
        
        let t: LookupVec<u8> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);        
        assert_eq!(r, expected);

        // fr the u16, we need a much longer segment
        let bits = create_bitvector(vec![ 
            1,1,1,1,1,1,1,1,
            0,1,1,1,0,1,1,1,
            1]).to_bitvec();
        let expected = vec![1,1,1,1, 2, 4, 1];

        let t: LookupVec<u16> = LookupVec::new();
        let r = fast_decode(&bits,false, &t);        
        assert_eq!(r, expected);
    }

    // #[test]
    #[allow(dead_code)]
    fn test_fast_speed() {
        let b = random_fibonacci_stream(10_000_000, 100000, 1000000, 123);
        // make a copy for fast decoder
        let mut b_fast: MyBitVector = BitVec::new();
        for bit in b.iter().by_vals() {
            b_fast.push(bit);
        }

        let t: LookupVec<u8> = LookupVec::new();
        let x2 = fast_decode(&b_fast, false,&t);   

        println!("{}", x2.iter().sum::<u64>());

        let t: LookupVec<u16> = LookupVec::new();
        let x2 = fast_decode(&b_fast, false,&t);   
        println!("{}", x2.iter().sum::<u64>())    ;
    }
}

/// Lazy `LookupTable` with `u8` segment size.
/// This table gets calculated once for the crate, can be reused many times for decoding.
pub static FB_LOOKUP_U8: Lazy<LookupVec<u8>> = Lazy::new(|| {
    println!("FB_LOOKUP_U8: initializing fibonacci lookup");
    let lookup = LookupVec::new();
    println!("FB_LOOKUP_U8: done initializing fibonacci lookup");
    lookup
});

/// Lazy `LookupTable` with `u16` segment size.
/// This table gets calculated once for the crate, can be reused many times for decoding.
pub static FB_LOOKUP_U16: Lazy<LookupVec<u16>> = Lazy::new(|| {
    println!("FB_LOOKUP_U16: initializing fibonacci lookup");
    let lookup = LookupVec::new();
    println!("FB_LOOKUP_U16: done initializing fibonacci lookup");
    lookup
});

/// Create a `FastDecoder` (internally decoding chunks of 8bits)
/// 
/// Fibonacci decoding cannot handle zeros, and often during the encoding, every value is incremented by one (to encode zero as 1).
/// If `shifted_by_one` is `true`, we decrement each decoded value by 1, assuming that the encoder artificially incremented each value before encoding. 
#[must_use]
pub fn get_u8_decoder(bistream: & MyBitSlice, shifted_by_one: bool) -> FastFibonacciDecoder<'_, u8> {
    FastFibonacciDecoder::new(bistream, shifted_by_one, &FB_LOOKUP_U8)
}

/// Create a FastDecoder (internally decoding chunks of 16bits)
/// 
/// Fibonacci decoding cannot handle zeros, and often during the encoding, every value is incremented by one (to encode zero as 1).
/// If `shifted_by_one` is `true`, we decrement each decoded value by 1, assuming that the encoder artificially incremented each value before encoding. 
#[must_use]
pub fn get_u16_decoder(bistream: &MyBitSlice, shifted_by_one: bool) -> FastFibonacciDecoder<'_, u16> {
    FastFibonacciDecoder::new(bistream, shifted_by_one, &FB_LOOKUP_U16)
}

/// Fast Fibonacci decoding via an iterator. Let's you decode one element after the other,
/// whereas [`fast_decode`] decodes the entire stream at once.
/// Using the iterator can be useful if the length of the binary-fibonacci code is not known, 
/// just the number of elements.
///
/// # Example
/// ```rust,
/// use fastfibonacci::bit_decode::fast::{FastFibonacciDecoder, LookupVec};
/// use bitvec::prelude as bv;
/// let bits = bv::bits![u8, bv::Msb0;
///     1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,
///     0,1,1,1,0,0,1,0].to_bitvec();
/// // second argument allows for automatic shifing the decoded values by -1
/// // (in case the encoding used +1 to be able to encode 0)
/// let table: LookupVec<u8> = LookupVec::new();
/// let f = FastFibonacciDecoder::new(&bits, false, &table);
///
/// let x = f.collect::<Vec<_>>();
/// assert_eq!(x, vec![4,7, 86]);
///
/// // on can still use the remaining buffer for other things:
/// // use fastfibonacci::FbDec;
/// // let r = f.get_remaining_buffer();
/// // assert_eq!(r, &bits[19..]);        
/// ```
pub struct FastFibonacciDecoder<'a, T> {
    bistream: &'a MyBitSlice, // bitstream to decode
    position: usize,
    lookup_table: &'a LookupVec<T>,
    segment_size: usize,
    /// decoded numbers not yet emitted
    current_buffer: VecDeque<Option<u64>>, 
    /// for each decoded number in `current_buffer`, remember how many bits its encoding was
    current_backtrack: VecDeque<Option<usize>>, 
    state: State,
    decoding_state: DecodingState,
    // position in bitstream after the last emission;
    // None if we exhausted the stream completely,
    // i.e. the stream ended with a terminator and we emitted that item
    last_emission_last_position: Option<usize>,
    shifted_by_one: bool,
}

impl<'a, T:Integral> FastFibonacciDecoder<'a, T> {
    /// New `FastFibonacciDecoder` decoding the bitstream with the given lookup table.
    /// 
    /// # Parameters
    /// - `bitstream`: (possibly infinite) sequence of bits containing fibonacci encoded u64s
    /// - `shifted_by_one`: if True, values are decremented by one (in case the encoding used a +1 shift to encode 0)
    pub fn new(bistream: &'a MyBitSlice, shifted_by_one: bool, lookup_table: &'a LookupVec<T>) -> Self {
        FastFibonacciDecoder {
            bistream,
            position: 0,
            lookup_table,
            current_buffer: VecDeque::new(),
            current_backtrack: VecDeque::new(),
            segment_size: T::BITS as usize,
            state: State(false),
            decoding_state: DecodingState::new(),
            last_emission_last_position: None,
            shifted_by_one,
        }
    }

    /// !!perf critical code!!
    /// decodes the next segment, adding to `current_buffer` and `current_backtrack`
    /// if theres nothgin to any more load (emtpy buffer, or partial buffer with some elements, but no terminator)
    /// it adds a None to `current_buffer` and `current_backtrack`, indicating the end of the iterator
    fn load_segment(&mut self) {
        // try to pull in the next segment
        // let segment = self.get_next_segment();
        let start = self.position;
        let end = cmp::min(self.position + self.segment_size, self.bistream.len());
        let segment = &self.bistream[start..end];
        // println!("Loading new segment: {}", bitstream_to_string(segment));
        self.position += self.segment_size;

        if segment.is_empty() {
            // add the terminator into the iterator
            self.current_buffer.push_back(None);
            self.current_backtrack.push_back(None);
            return;
        }

        // decode this segment
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
        // no need to do anything!
        if segment.len() < self.segment_size {
            segment_int <<= self.segment_size - segment.len();
        }

        let (newstate, result) = self.lookup_table.lookup(self.state, segment_int);
        self.state = newstate;
        self.decoding_state.update(result);

        // println!("Segment: {}, SegmentInt {}", segment, segment_int);
        // println!("Decoded state: {:?}, result {:?}", newstate, result);

        // println!("Decoding state: {:?}", self.decoding_state);
        // move all decoded numbers into the emission buffer

        // todo: feels like this copy/move is unneeded,
        // we could just pop of self.decoding_state.decoded_numbers directly when emitting for the iterator
        for el in self.decoding_state.decoded_numbers.drain(0..self.decoding_state.decoded_numbers.len()) {
            self.current_buffer.push_back(Some(el));
        }
        // move all decoded number-starts into the emission buffer
        // no need to delete in result, gets dropped
        for &el in &result.number_end_in_segment {
            self.current_backtrack.push_back(Some(el + start)); // turn the relative (to segment start) into an absolute postion
        }
        assert!(self.decoding_state.decoded_numbers.is_empty());

        // println!("current buffer: {:?}", self.current_buffer);

        if segment.len() != self.segment_size {
            // println!("partial segment");
            // a truncated segment, i.e. the last segment
            // push the terminator into the iterator to signal we;re done
            self.current_buffer.push_back(None);
            self.current_backtrack.push_back(None);
        }
    }
}

impl<'a, T:Integral> FbDec<'a> for FastFibonacciDecoder<'a, T> {
    /// return the remaining bitstream after the last yielded number.
    /// If the bitstream is fully exhausted (i.e. no remainder), returns an empty bitslice.
    fn get_remaining_buffer(&self) -> &'a MyBitSlice {
        match self.last_emission_last_position {
            Some(pos) => &self.bistream[pos + 1..],
            None => self.bistream, // no single element was emitted, hence no bits of the stream affected
        }
    }

    /// Points to the first bit after the last terminator:
    /// ```bash
    /// ..011x...
    ///      ^
    /// ```
    /// If nothing was processed, or no single u64 could be decoded (no terminator),
    /// points to the first bit in the string.
    fn get_bits_processed(&self) -> usize {
        match self.last_emission_last_position {
            Some(pos) => pos + 1,
            None => 0, // no single element was emitted, hence no bits of the stream affected
        }
    }
}

/// The iterator is a bit complicated! We can't decode a single number
/// (as the fast algorithm will potentially yield multiple numbers per segment),
/// only an entire segment, hence we need to buffer the decoded numbers, yielding
/// them one by one.
impl<'a, T:Integral> Iterator for FastFibonacciDecoder<'a, T> {
    type Item = u64;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.current_buffer.is_empty() {
            // could be that we need to load multiple segments until we gind a terminator!
            self.load_segment();
        }
        // } else {
        //     println!("non-empty buffer: just yielding what we have already: {:?} starts: {:?}", self.current_buffer, self.current_backtrack);
        // }
        // let el = self.current_buffer.remove(0); // TODO: expensive, Deque instead?
        // let _dummy = self.current_backtrack.remove(0); // TODO: expensive, Deque instead?
        // self.last_emission_last_position = _dummy;

        let el = self.current_buffer.pop_front().unwrap(); // unwrap should be save, there HAS to be an element
        let dummy = self.current_backtrack.pop_front().unwrap(); // unwrap should be save, there HAS to be an element

        // we only update the last elements position if we actually emit an item
        // if were just emitting the Iteration-TRM, the position of the last element remains unchanged
        if let Some(i) = dummy {
            self.last_emission_last_position = Some(i);
        };

        // println!("State after emission: Position {}, LastPos {:?}, Buffer {:?} starts: {:?}", self.position, self.last_emission_last_position, self.current_buffer, self.current_backtrack);
        if self.shifted_by_one {
            el.map(|x| x - 1)
        } else {
            el
        }

    }
}

#[cfg(test)]
mod test_iter {
    use super::*;
    use crate::utils::create_bitvector;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_iter() {
        // just a 3number stream, trailing stuff
        let bits = create_bitvector(vec![ 
            1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0])
        .to_bitvec();
        let f: FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        let x = f.collect::<Vec<_>>();
        assert_eq!(x, vec![4, 7, 86]);

        let f: FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        let x = f.collect::<Vec<_>>();
        assert_eq!(x, vec![4, 7, 86]);
    }

    #[test]
    fn test_fast_decode_shift() {

        let bits = create_bitvector(vec![ 
            1,1,   // 0
            0,1,1, // 1
            0,0,1,1// 2
        ]).to_bitvec();

        let f: FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, true, &FB_LOOKUP_U8);
        let x = f.collect::<Vec<_>>();
        assert_eq!(x, vec![0, 1, 2]);
    }
    #[test]
    fn test_iter_multiple_segments() {
        // what if not a single number is decoded per segment
        let bits = create_bitvector(vec![ 
            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0])
        .to_bitvec();
        let mut f: FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(4181));
        assert_eq!(f.get_remaining_buffer(), &bits[19..]);


        let mut f: FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        assert_eq!(f.next(), Some(4181));
        assert_eq!(f.get_remaining_buffer(), &bits[19..]);

        let bits = create_bitvector(vec![ 
            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,
            1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0])
        .to_bitvec();
        let mut f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(1597));
        assert_eq!(f.get_remaining_buffer(), &bits[17..]);

        let mut f:FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        assert_eq!(f.next(), Some(1597));
        assert_eq!(f.get_remaining_buffer(), &bits[17..]);
    }

    #[test]
    fn test_iter_exact_borders() {
        // just a 3number stream, no trailing
        let bits = create_bitvector(vec![
            1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,  // 4, 7, 86
            0,1,1,1,0,0,1,1,0,1,1,1,0,0,1,1  // 3, 2, 4
        ])
        .to_bitvec();

        let f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        let x = f.collect::<Vec<_>>();
        assert_eq!(x, vec![4, 7, 86, 6, 2, 6]);

        let f:FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        let x = f.collect::<Vec<_>>();
        assert_eq!(x, vec![4, 7, 86, 6, 2, 6]);
    }
    #[test]
    fn test_iter_remaining_stream() {
        // just a 3number stream, no trailing
        let bits = create_bitvector(vec![ 
            1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0])
        .to_bitvec();

        let mut f: FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(4));
        assert_eq!(f.get_bits_processed(), 4);
        assert_eq!(f.get_remaining_buffer(), &bits[4..]);

        let mut f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(4));
        assert_eq!(f.next(), Some(7));
        assert_eq!(f.get_bits_processed(), 9);
        assert_eq!(f.get_remaining_buffer(), &bits[9..]);

        let mut f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(4));
        assert_eq!(f.next(), Some(7));
        assert_eq!(f.next(), Some(86));
        assert_eq!(f.get_bits_processed(), 19);
        assert_eq!(f.get_remaining_buffer(), &bits[19..]);

        let mut f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), Some(4));
        assert_eq!(f.next(), Some(7));
        assert_eq!(f.next(), Some(86));
        assert_eq!(f.next(), None);
        assert_eq!(f.get_bits_processed(), 19);
        assert_eq!(f.get_remaining_buffer(), &bits[19..]);

        let mut f:FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        assert_eq!(f.next(), Some(4));
        assert_eq!(f.next(), Some(7));
        assert_eq!(f.next(), Some(86));
        assert_eq!(f.next(), None);
        assert_eq!(f.get_bits_processed(), 19);
        assert_eq!(f.get_remaining_buffer(), &bits[19..]);
    }

    #[test]
    fn test_iter_remaining_stream_nobits_processed() {
        // no terminator anywhere
        let bits = create_bitvector(vec![ 
        1,0,0,1,0,1,0,0,1,0,1,0,0,1,0,1,
        0,1,0,1,0,0,1,0])
        .to_bitvec();

        let mut f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U8);
        assert_eq!(f.next(), None);
        assert_eq!(f.get_bits_processed(), 0);
        assert_eq!(f.get_remaining_buffer(), &bits);

        let mut f:FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&bits, false, &FB_LOOKUP_U16);
        assert_eq!(f.next(), None);
        assert_eq!(f.get_bits_processed(), 0);
        assert_eq!(f.get_remaining_buffer(), &bits);
    }
}
