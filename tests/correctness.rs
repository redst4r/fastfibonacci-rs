use bitvec::vec::BitVec;
use fastfibonacci::{bit_decode::{fast::{fast_decode, LookupVec, FB_LOOKUP_U16, FB_LOOKUP_U8}, fibonacci::FibonacciDecoder, MyBitVector}, byte_decode::{bare_metal_16single_faster::U16Fast, bare_metal_generic_single::{DirtyGenericSingle, U64DecoderGeneric}, byte_manipulation::bits_to_fibonacci_generic_array_u64, bytestream_transform::{U64BytesToU16, U64BytesToU64, U64BytesToU8}, faster::{FastFibonacciDecoderNewU16, FastFibonacciDecoderNewU8, LookupVecNew}}, fast_decode_new, utils::random_fibonacci_stream, FastFibonacciDecoder, U64Decoder};


// create some random numbers, encode and return
// as u8 bytestream and the true decoding
fn create_random() -> (Vec<u8>, Vec<u64>){
    let bits = random_fibonacci_stream(100_000, 1, 10000, 123455);
    let bytes = bits_to_fibonacci_generic_array_u64(&bits);

    // ground thruth
    let dec = FibonacciDecoder::new(&bits, false);
    let x_true: Vec<_> = dec.collect();

    (bytes ,x_true)
}

#[test]
fn test_correctness_u64_decoder() {
    let (bytes ,x_true) = create_random();
    let dd = U64Decoder::new(bytes.as_slice());
    let x2: Vec<_> = dd.collect();
    assert_eq!(x_true, x2);
}

#[test]
fn test_correctness_fast_decode_u8() {
    let (bytes ,x_true) = create_random();

    let x_u8: Vec<u8> = U64BytesToU8::new(bytes.as_slice()).collect();
    let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).collect();

    let t: LookupVecNew<u8> = LookupVecNew::new();
    let x2 = fast_decode_new(&x_u8,false, &t);        
    assert_eq!(x_true, x2);


    let t: LookupVecNew<u16> = LookupVecNew::new();
    let x2 = fast_decode_new(&x_u16,false, &t);        
    assert_eq!(x_true, x2);
}

mod test_dirty_generic_single{
    use super::*;
    #[test]
    fn test_correctness_dirty64(){
        let (bytes ,x_true) = create_random();
        let encoded_bytes: Vec<u64> = U64BytesToU64::new(bytes.as_slice()).collect();
        // println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
        let mut decoded = Vec::with_capacity(x_true.len());

        let mut last_partial = Default::default();
        for _i in 0..encoded_bytes.len() {
            let mut dd: DirtyGenericSingle<u64> = DirtyGenericSingle::new(encoded_bytes[_i]);

            let (numbers, pa) = dd.decode_all_from_partial(last_partial);
            decoded.extend(numbers);
            last_partial = pa;
        }

        assert_eq!(x_true, decoded);
    }

    // #[test]
    // fn test_correctness_dirty32(){
    //     let (bytes ,x_true) = create_random();
        
    //     let x_u32: Vec<u32> = U64BytesToU32::new(bytes.as_slice()).flatten().collect();        
    //     // println!("{}", bitstream_to_string_pretty(&data_encoded, 32));
    //     let mut decoded = Vec::new();

    //     let mut last_partial = Default::default();
    //     for _i in 0..x_u32.len() {
    //         let mut dd: DirtyGenericSingle<u32> = DirtyGenericSingle::new(x_u32[_i]);

    //         let (numbers, pa) = dd.decode_all_from_partial(last_partial);
    //         decoded.extend(numbers);
    //         last_partial = pa;
    //     }
    //     assert_eq!(x_true, decoded);
    // }	

    #[test]
    fn test_correctness_dirty16(){
        let (bytes ,x_true) = create_random();

        let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).collect();
        // println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
        let mut decoded = Vec::new();

        let mut last_partial = Default::default();
        for _i in 0..x_u16.len() {
            let mut dd: DirtyGenericSingle<u16> = DirtyGenericSingle::new(x_u16[_i]);

            let (numbers, pa) = dd.decode_all_from_partial(last_partial);
            decoded.extend(numbers);
            last_partial = pa;
        }
        assert_eq!(x_true, decoded);
    }

    #[test]
    fn test_correctness_dirty8(){
        let (bytes ,x_true) = create_random();

        let x_u8: Vec<u8> = U64BytesToU8::new(bytes.as_slice()).collect();
        
        let mut decoded = Vec::new();

        let mut last_partial = Default::default();
        for _i in 0..x_u8.len() {
            let mut dd: DirtyGenericSingle<u8> = DirtyGenericSingle::new(x_u8[_i]);


            let (numbers, pa) = dd.decode_all_from_partial(last_partial);
            decoded.extend(numbers);
            last_partial = pa;
        }
        assert_eq!(x_true, decoded);
    }
}


#[test]
fn test_correctness_u16_fast(){
    let (bytes ,x_true) = create_random();
    let x_u16: Vec<u16> = U64BytesToU16::new(bytes.as_slice()).collect();
    let table = LookupVecNew::new();

    // println!("{}", bitstream_to_string_pretty(&data_encoded, 64));
    let mut decoded = Vec::new();

    let mut last_partial = Default::default();
    for _i in 0..x_u16.len() {
        let mut dd = U16Fast::new(x_u16[_i], &table);

        let (numbers, pa) = dd.decode_all_from_partial(&last_partial);
        decoded.extend(numbers);
        last_partial = pa;
    }
    assert_eq!(x_true, decoded);
}

#[test]
fn test_correctness() {
    let (bytes ,x_true) = create_random();

	let dd = U64DecoderGeneric::new(bytes.as_slice());
	let x2: Vec<_> = dd.collect();
  
	assert_eq!(x_true, x2);
}


#[test]
fn test_fast_fibonacci_decoder_new_u8_correct(){
    let (bytes ,x_true) = create_random();
    let table: LookupVecNew<u8> = LookupVecNew::new();

    let dd = FastFibonacciDecoderNewU8::new(bytes.as_slice(), &table, false, fastfibonacci::byte_decode::faster::StreamType::U64);
	let x2: Vec<_> = dd.collect();
  
	assert_eq!(x_true, x2);
}

#[test]
fn test_fast_fibonacci_decoder_new_u16_correct(){
    let (bytes ,x_true) = create_random();
    let table: LookupVecNew<u16> = LookupVecNew::new();

    let dd = FastFibonacciDecoderNewU16::new(bytes.as_slice(), &table, false, fastfibonacci::byte_decode::faster::StreamType::U64);
	let x2: Vec<_> = dd.collect();
  
	assert_eq!(x_true, x2);
}


#[test]
fn test_correctness_fibonacci_decoder() {
    use fastfibonacci::bit_decode::fibonacci::FibonacciDecoder;
    let b = random_fibonacci_stream(100000, 1, 1000, 123);
    // make a copy for fast decoder
    let mut b_fast: MyBitVector = BitVec::new();
    for bit in b.iter().by_vals() {
        b_fast.push(bit);
    }
    let dec = FibonacciDecoder::new(&b, false);
    let x1: Vec<_> = dec.collect();

    let f:FastFibonacciDecoder<'_, u8> = FastFibonacciDecoder::new(&b_fast, false, &FB_LOOKUP_U8);
    let x2: Vec<_> = f.collect();

    assert_eq!(x1, x2);

    let f:FastFibonacciDecoder<'_, u16> = FastFibonacciDecoder::new(&b_fast, false, &FB_LOOKUP_U16);
    let x3: Vec<_> = f.collect();
    assert_eq!(x1, x3);
}

#[test]
fn test_correctness_fast_decode_u8_fibonacci_decoder() {
    use fastfibonacci::bit_decode::fibonacci::FibonacciDecoder;
    let b = random_fibonacci_stream(100000, 1, 1000, 123);
    // make a copy for fast decoder
    let mut b_fast: MyBitVector = BitVec::new();
    for bit in b.iter().by_vals() {
        b_fast.push(bit);
    }
    let dec = FibonacciDecoder::new(&b, false);
    let x1: Vec<_> = dec.collect();

    let t: LookupVec<u8> = LookupVec::new();
    let x2 = fast_decode(&b_fast,false, &t);        
    assert_eq!(x1, x2);

    let t: LookupVec<u16> = LookupVec::new();
    let x2 = fast_decode(&b_fast,false, &t);        
    assert_eq!(x1, x2);
}

#[test]
fn test_correctness_fast_decode() {
    use fastfibonacci::bit_decode::fibonacci::FibonacciDecoder;
    let b = random_fibonacci_stream(100000, 1, 1000, 123);

    let t8: LookupVec<u8> = LookupVec::new();
    let t16: LookupVec<u16> = LookupVec::new();

    let dec = FibonacciDecoder::new(&b, false);
    let x1: Vec<_> = dec.collect();

    let x2 = fast_decode(&b,false, &t8);
    assert_eq!(x1, x2);

    let x3 = fast_decode(&b,false, &t16);
    assert_eq!(x1, x3);
}