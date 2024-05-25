//! Fast fibonacci decoding using lookup tables.
use std::collections::VecDeque;
use std::io::Read;
use std::iter::Flatten;
use std::marker::PhantomData;
use funty::Integral;
use crate::byte_decode::{bare_metal_generic_single::DirtyGenericSingle,  partial::Partial};
use crate::fastutils::State;
use super::chunker::{U64BytesToU16, U64BytesToU8};
use super::partial::number_plus_partial;
use once_cell::sync::Lazy;


#[derive(Debug)]
/// A lookup table for fast-fibonacci decoding. For a given segment of bits (represented as a u8/u16, depending in T),
/// look up what numbers those bits encode and what de partial decoding looks like
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


/// Lazy LookupTable with u8 segment size.
/// This table gets calculated once for the crate, can be reused many times for decoding.
pub static FB_LOOKUP_NEW_U8: Lazy<LookupVecNew<u8>> = Lazy::new(|| {
    println!("initializing fibonacci lookup");
    let lookup = LookupVecNew::new();
    println!("done initializing fibonacci lookup");
    lookup
});

/// Lazy LookupTable with u16 segment size.
/// This table gets calculated once for the crate, can be reused many times for decoding.
pub static FB_LOOKUP_NEW_U16: Lazy<LookupVecNew<u16>> = Lazy::new(|| {
    println!("initializing fibonacci lookup");
    let lookup = LookupVecNew::new();
    println!("done initializing fibonacci lookup");
    lookup
});

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
            newp.combine_partial(&partial);
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


#[cfg(test)]
mod test {
    use crate::{byte_decode::byte_manipulation::bits_to_fibonacci_generic_array, utils::create_bitvector};
    use super::*;
    #[test]
    fn test_fast_decode() {

        // the exampel from the paper, Fig 9.4
        let bits = create_bitvector(vec![ 
            1,0,1,1,0,1,0,1,
            1,0,1,0,0,1,0,1,
            0,1,1,1,0,0,1,0]).to_bitvec();

        let bytes = bits_to_fibonacci_generic_array(&bits);
        let x_u8: Vec<u8> = U64BytesToU8::new(bytes.as_slice()).flatten().collect();
        let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).flatten().collect();

        let t: LookupVecNew<u8> = LookupVecNew::new();
        let r = fast_decode_new(&x_u8,false, &t);
        assert_eq!(r, vec![4,7, 86]);

        let t: LookupVecNew<u16> = LookupVecNew::new();
        let r = fast_decode_new(&x_u16,false, &t);
        assert_eq!(r, vec![4,7, 86]);
    }
}


/// Wether the byte stream originates from u64 or u32
pub enum StreamType {
    /// u64 
    U64,
    ///  u32
    U32
}
/// Takes in a stream of bytes, decoding chunks of those using a lookup table.
/// 
/// Things are complicated: The stream of bytes usually is in groups of 8 (u64s),
/// (but sometimes can be u32), and comes in **LittleEndian**, i.e. the 8th byte needs to be 
/// decoded first, then the 7th...
/// [Dirty64Single] does it right automatically as it only operates on the u64 (not the bytes).
/// However, with fast decoding we look at 1byte (u8) or two bytes (u16)
/// 
/// 
pub struct FastFibonacciDecoderNewU8<'a, R:Read> {
    //stream to decode, chunked into the right pieces to be fed into lookup table
    stream: Flatten<U64BytesToU8<R>>, 
    lookup_table: &'a LookupVecNew<u8>,
    // decoded numbers not yet emitted; once there's no new numbers, adds a `None` as terminator
    current_buffer: VecDeque<Option<u64>>,
    shifted_by_one: bool,
    partial: Partial,
}

impl<'a, R:Read>  FastFibonacciDecoderNewU8<'a, R> {
    /// Creates a new decoder
    pub fn new(stream: R, lookup_table: &'a LookupVecNew<u8>, shifted_by_one: bool, streamtype: StreamType) ->Self {
        let chunked_u8_stream = match streamtype {
            StreamType::U64 => {
                // things come in as 12345678|ABCDEFGH
                // `8` is the byte that we need to look at first.
                // we use the ChunksU64ToU8 to get the order of bytes right for decoding
                U64BytesToU8::new(stream).flatten() // note: ChunksU64ToU8 returns [u8;8], but we need to emit byte by byte! hence the flatten
            },
            StreamType::U32 => todo!(),
        };
        Self {
            stream: chunked_u8_stream,
            lookup_table,
            current_buffer: VecDeque::with_capacity(8),
            shifted_by_one,
            partial: Default::default(),
        }
    }

    /// pull another segment from the stream, decode
    pub fn load_segment(&mut self) {

        match self.stream.next() {
            Some(segment_int) => {
                // decode the segment

                // need to pad
                // actually dont!
                // let segment_int_pad = padding(segment_int);
                let segment_int_pad = segment_int;
                let (numbers, p) = self.lookup_table.lookup(State(self.partial.last_bit as usize), segment_int_pad);

                // now, we need to properly decode those numbers:
                // if the previous segment left over something (see partial)
                // we need to "add" this to numbers[0]
                // if not, we need to merge p (the new partial decode from stream[i]) and partial (the old partial decode from stream(i-1))
                if !numbers.is_empty() {
                    // println!("Combining {numbers:?} with {partial:?}");
                    // absorb `partial` (the old decoding) into the number
                    // and keep the new decoding status as is
                    let new_x = number_plus_partial(numbers[0], &self.partial);
                    // println!("newx {new_x}");
                    self.current_buffer.push_back(Some(new_x));
                    self.current_buffer.extend(numbers[1..].iter().map(|&x| Some(x)));
                    // decoded_numbers.extend(&numbers[1..]);


                    // numbers[0] = new_x;
                    self.partial = p.clone();
                } else {
                    // "add" p and partial; ORDER is important
                    // partial = combine_partial(partial, p)
                    let mut newp = p.clone();
                    newp.combine_partial(&self.partial);
                    self.partial = newp;
                }
            }
            None => {
                // no more segments in stream
                // assert that there's no leftovers in the current decoding
                // and add None to buffer
                assert!(self.partial.is_clean());
                self.current_buffer.push_back(None);
            }
        }
    }
    /// IS the decoder in a clean state, i.e. no unemitted items and no more partial decoding
    pub fn is_clean(&self) -> bool {
        self.current_buffer.is_empty() && self.partial.is_clean()
    }
}

impl<'a, R:Read> Iterator for FastFibonacciDecoderNewU8<'a, R> {
    type Item=u64;

    fn next(&mut self) -> Option<Self::Item> {

        // pull in new elements until we get something in the buffer to emit
        while self.current_buffer.is_empty() {
            self.load_segment()
        }

        let el = self.current_buffer.pop_front().unwrap(); // unwrap should be save, there HAS to be an element

        if self.shifted_by_one {
            el.map(|x| x - 1)
        } else {
            el
        }
    }
}

#[test]
fn test_fixed_(){
    // this corresponds to a single entry [7]
    // 01011000_000...
    let bytes =vec![0,0,0,0,0,0,0,88]; 
    let t: LookupVecNew<u8> = LookupVecNew::new();
    let mut dd = FastFibonacciDecoderNewU8::new(bytes.as_slice(), &t, false, StreamType::U64);
    let x = dd.next();
    assert_eq!(x, Some(7));

    let bytes =vec![0,0,0,0,0,0,192,90]; 
    let t: LookupVecNew<u8> = LookupVecNew::new();
    let mut dd = FastFibonacciDecoderNewU8::new(bytes.as_slice(), &t, false, StreamType::U64);
    let x = dd.next();
    assert_eq!(x, Some(7));
    let x = dd.next();
    assert_eq!(x, Some(7));
    let x = dd.next();
    assert_eq!(x, None);
}


/// A Fast decoder for the bytestream, using a u16-lookup table. See [`FastFibonacciDecoderNewU8`].
pub struct FastFibonacciDecoderNewU16<'a, R:Read> {
    //stream to decode, chunked into the right pieces to be fed into lookup table
    stream: Flatten<U64BytesToU16<R>>, 
    lookup_table: &'a LookupVecNew<u16>,
    // decoded numbers not yet emitted; once there's no new numbers, adds a `None` as terminator
    current_buffer: VecDeque<Option<u64>>,
    shifted_by_one: bool,
    partial: Partial,
}

impl<'a, R:Read>  FastFibonacciDecoderNewU16<'a, R> {
    /// Create a new FastDecoder
    pub fn new(stream: R, lookup_table: &'a LookupVecNew<u16>, shifted_by_one: bool, streamtype: StreamType) ->Self {
        let chunked_u16_stream = match streamtype {
            StreamType::U64 => {
                // things come in as 12345678|ABCDEFGH
                // `8` is the byte that we need to look at first.
                // we use the ChunksU64ToU8 to get the order of bytes right for decoding
                U64BytesToU16::new(stream).flatten() // note: ChunksU64ToU8 returns [u8;8], but we need to emit byte by byte! hence the flatten
            },
            StreamType::U32 => todo!(),
        };
        Self {
            stream: chunked_u16_stream,
            lookup_table,
            current_buffer: VecDeque::with_capacity(8), // the maximum number of elements decocded at once is 8: 11111111_11111111
            shifted_by_one,
            partial: Default::default(),
        }
    }

    /// pull another segment from the stream, decode
    pub fn load_segment(&mut self) {

        // as load_Segment only gets called when the buffer is empty
        // assert_eq!(self.current_buffer.len(), 0);

        match self.stream.next() {
            Some(segment_int) => {
                // decode the segment

                // need to pad
                // actually dont!
                // let segment_int_pad = padding(segment_int);
                let segment_int_pad = segment_int;
                let (numbers, p) = self.lookup_table.lookup(State(self.partial.last_bit as usize), segment_int_pad);

                // now, we need to properly decode those numbers:
                // if the previous segment left over something (see partial)
                // we need to "add" this to numbers[0]
                // if not, we need to merge p (the new partial decode from stream[i]) and partial (the old partial decode from stream(i-1))
                if !numbers.is_empty() {
                    // println!("Combining {numbers:?} with {partial:?}");
                    // absorb `partial` (the old decoding) into the number
                    // and keep the new decoding status as is
                    let new_x = number_plus_partial(numbers[0], &self.partial);
                    // println!("newx {new_x}");
                    self.current_buffer.push_back(Some(new_x));
                    self.current_buffer.extend(numbers[1..].iter().map(|&x| Some(x)));
                    // decoded_numbers.extend(&numbers[1..]);

                    self.partial = p.clone();
                } else {
                    // "add" p and partial; ORDER is important
                    // partial = combine_partial(partial, p)
                    let mut newp = p.clone();
                    newp.combine_partial(&self.partial);
                    self.partial = newp;
                }
            }
            None => {
                // no more segments in stream
                // assert that there's no leftovers in the current decoding
                // and add None to buffer
                assert!(self.partial.is_clean());
                self.current_buffer.push_back(None);
            }
        }
    }
    /// IS the decoder in a clean state, i.e. no unemitted items and no more partial decoding
    pub fn is_clean(&self) -> bool {
        self.current_buffer.is_empty() && self.partial.is_clean()
    }
}


impl<'a, R:Read> Iterator for FastFibonacciDecoderNewU16<'a, R> {
    type Item=u64;

    fn next(&mut self) -> Option<Self::Item> {


        // pull in new elements until we get something in the buffer to emit
        while self.current_buffer.is_empty() {
            self.load_segment()
        }

        let el = self.current_buffer.pop_front().unwrap(); // unwrap should be save, there HAS to be an element

        if self.shifted_by_one {
            el.map(|x| x - 1)
        } else {
            el
        }
    }
}

#[test]
fn test_fixed_u16(){
    // this corresponds to a single entry [7]
    // 01011000_000...
    let bytes =vec![0,0,0,0,0,0,0,88]; 
    let t: LookupVecNew<u16> = LookupVecNew::new();
    let mut dd = FastFibonacciDecoderNewU16::new(bytes.as_slice(), &t, false, StreamType::U64);
    let x = dd.next();
    
    assert_eq!(x, Some(7));


    let bytes =vec![0,0,0,0,0,0,192,90]; 
    let t: LookupVecNew<u16> = LookupVecNew::new();
    let mut dd = FastFibonacciDecoderNewU16::new(bytes.as_slice(), &t, false, StreamType::U64);
    let x = dd.next();
    
    assert_eq!(x, Some(7));
    let x = dd.next();
    assert_eq!(x, Some(7));

    let x = dd.next();
    assert_eq!(x, None);
}