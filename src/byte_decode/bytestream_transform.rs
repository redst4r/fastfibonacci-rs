//! Utilities to deal with bytestreams originating from streams of uints.
//! 
//! Assumes that the bytes in the intput stream actualyl come from a stream
//! of u32/u64 and hence the bytes need to be reordered in groups of 4/8 
use std::io::ErrorKind;
use std::io::Read;
use byteorder::LittleEndian;
use byteorder::BigEndian;
use byteorder::ReadBytesExt;


/// Marks any Transformer that turns things into a u8 stream
pub (crate) trait IntoU8Transform<R> {
    /// yield the next u8
    fn next_u8(&mut self) -> Option<u8>; 

    // how many u8 have been yieled
    fn get_consumed_bytes(&self) -> usize;
}

impl <R:Read> IntoU8Transform<R> for U64BytesToU8<R> {
    fn next_u8(&mut self) -> Option<u8> {
        self.next()
    }
    
    fn get_consumed_bytes(&self) -> usize {
        self.bytes_consumed
    }
}

impl <R:Read> IntoU8Transform<R> for U32BytesToU8<R> {
    fn next_u8(&mut self) -> Option<u8> {
        self.next()
    }
    fn get_consumed_bytes(&self) -> usize {
        self.bytes_consumed
    }
}

/// Marks any Transformer that turns things into a u16 stream
pub (crate) trait IntoU16Transform<R> {
    fn next_u16(&mut self) -> Option<u16>; 
    fn get_consumed_bytes(&self) -> usize;
}

impl <R:Read> IntoU16Transform<R> for U64BytesToU16<R> {
    fn next_u16(&mut self) -> Option<u16> {
        self.next()
    }
    fn get_consumed_bytes(&self) -> usize {
        self.bytes_consumed
    }
}

impl <R:Read> IntoU16Transform<R> for U32BytesToU16<R> {
    fn next_u16(&mut self) -> Option<u16> {
        self.next()
    }
    fn get_consumed_bytes(&self) -> usize {
        self.bytes_consumed
    }
}

/// Turns a bytestream (&[u8], or any `Read`) into a stream of U64s. Assumes little endian bytestream.
/// 
/// Note, if the stream is NOT a multiple of 8bytes, it'll drop the remainder!
pub struct U64BytesToU64<R> {
    read: R,
}

impl<R:Read> U64BytesToU64<R> {
    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read }
    }
    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        self.read
    }
}

impl<R:Read> Iterator for U64BytesToU64<R> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let u = self.read.read_u64::<LittleEndian>();
        match u {
            Ok(n) => Some(n),
            Err(e) => {
                match e.kind() {
                    ErrorKind::UnexpectedEof => None,
                    _ => panic!("io error"),
                }
            },
        }
    }
}


/// Consumes a bytestream (groups of 8, from u64s), returning it ready for FastFibnoacci decoding
/// in 1byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U64BytesToU8<R> {
    read: R,
    // each u64 will creatye a u8, but we emit them one by one
    // buf: Vec<u8>
    buf: [u8; 8],
    pos: usize,
    bytes_consumed: usize,
}

impl<R:Read> U64BytesToU8<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read, buf: [0_u8;8], pos: 8, bytes_consumed: 0}  // initialized with zeros, but pos is set to 8 so the first `next` will pull in new data
            // buf: Vec::with_capacity(8)}
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        // assert!(self.buf.is_empty());
        self.read
    }
}

impl<R:Read> Iterator for U64BytesToU8<R> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {

        if self.pos >= self.buf.len() {
            // load a new u64 from stream
            match self.read.read_u64::<LittleEndian>() {
                Ok(n) => {
                    let reversed_bytes = n.to_be_bytes();
                    self.buf = reversed_bytes;
                    self.pos = 0;
                    self.bytes_consumed += 8;
                },
                Err(e) => {
                    match e.kind() {
                        ErrorKind::UnexpectedEof => return None,
                        _ => panic!("io error"),
                    }
                }
            }
        }

        let el = self.buf[self.pos];
        self.pos += 1;
        Some(el)
    }
}


/// Consumes a bytestream, returning it ready for FastFibnoacci decoding
/// in 2byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U64BytesToU16<R> {
    read: R,
    buf: [u16; 4],
    pos: usize,
    bytes_consumed: usize,
}

impl<R:Read> U64BytesToU16<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self {
            read,
            buf: [0_u16; 4],
            pos: 4,
            bytes_consumed: 0
        }
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        self.read
    }
}


impl<R> Iterator for U64BytesToU16<R>
where R: Read, {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.buf.len() {
            // to proper way: load as little endian,
            // then invert 
            let u = self.read.read_u64::<LittleEndian>();
            match u {
                Ok(n) => {
                    let reversed_bytes = n.to_be_bytes();
                    let mut buf = [0_u16; 4];
                    reversed_bytes.as_slice().read_u16_into::<BigEndian>(&mut buf).unwrap();
                    self.buf = buf;
                    self.pos = 0;
                    self.bytes_consumed += 8;
                },
                Err(e) => {
                    match e.kind() {
                        ErrorKind::UnexpectedEof => return None,
                        _ => panic!("io error"),
                    }
                }
            }
        };
        let el = self.buf[self.pos];
        self.pos += 1;
        Some(el)
    }
}



/// Consumes a bytestream (groups of 8, from u64s), returning it ready for FastFibnoacci decoding
/// in 1byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U32BytesToU8<R> {
    read: R,
    // each u64 will creatye a u8, but we emit them one by one
    buf: [u8; 4],
    pos: usize,
    bytes_consumed: usize
}

impl<R:Read> U32BytesToU8<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read, buf: [0_u8;4], pos: 4, bytes_consumed: 0}
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        // assert!(self.buf.is_empty());
        self.read
    }
}

impl<R:Read> Iterator for U32BytesToU8<R> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {

        if self.pos >= self.buf.len() {
            // load a new u64 from stream
            match self.read.read_u32::<LittleEndian>() {
                Ok(n) => {
                    let reversed_bytes = n.to_be_bytes();
                    self.buf = reversed_bytes;
                    self.pos = 0;
                    self.bytes_consumed += 4;

                },
                Err(e) => {
                    match e.kind() {
                        ErrorKind::UnexpectedEof => return None,
                        _ => panic!("io error"),
                    }
                }
            }
        }

        let el = self.buf[self.pos];
        self.pos += 1;
        Some(el)
    }
}


/// Consumes a bytestream (groups of 8, from u64s), returning it ready for FastFibnoacci decoding
/// in 1byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U32BytesToU16<R> {
    read: R,
    // each u64 will creatye a u8, but we emit them one by one
    buf: [u16; 2],
    pos: usize,
    bytes_consumed: usize,
}

impl<R:Read> U32BytesToU16<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read, buf: [0_u16; 2], pos: 2, bytes_consumed: 0}
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        // assert!(self.buf.is_empty());
        self.read
    }
}

impl<R:Read> Iterator for U32BytesToU16<R> {
    type Item = u16;
    fn next(&mut self) -> Option<Self::Item> {

        if self.pos >= self.buf.len() {

            // to proper way: load as little endian,
            // then invert 
            let u = self.read.read_u32::<LittleEndian>();
            match u {
                Ok(n) => {
                    let reversed_bytes = n.to_be_bytes();
                    let mut buf = [0_u16; 2];
                    reversed_bytes.as_slice().read_u16_into::<BigEndian>(&mut buf).unwrap();
                    self.buf = buf;
                    self.pos = 0;
                    self.bytes_consumed += 4;
                },
                Err(e) => {
                    match e.kind() {
                        ErrorKind::UnexpectedEof => return None,
                        _ => panic!("io error"),
                    }
                },
            }
        };
        let el = self.buf[self.pos];
        self.pos += 1;
        Some(el)
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bytes_to_u64(){
        let bytes = vec![1_u8, 0, 0, 0,0,0,0,0];

        let mut c = U64BytesToU64::new(bytes.as_slice());

        assert_eq!(
            c.next(),
            Some(1)
        );
        assert_eq!(
            c.next(),
            None
        );
    }

    #[test]
    fn test_chunks_u64_to_u8(){
        let bytes = [1,2,3,4,5,6,7,8, 10,11,12,13,14,15,16,17,];
        let c = U64BytesToU8::new(bytes.as_slice());
        
        let x: Vec<_> = c.collect();
        assert_eq!(
            x,
            [8,7,6,5,4,3,2,1,17,16,15,14,13,12,11,10]
        );
    }

    #[test]
    fn test_chunks_u64_to_u16(){
        use crate::byte_decode::byte_manipulation::read_bit_u16;
        
        let bytes = [4,0,3,0,2,0,1,0];
        let c = U64BytesToU16::new(bytes.as_slice());

        let x: Vec<_> = c.collect();
        assert_eq!(
            x,
            [1,2,3,4]
        );

        //this encodes [7,7]: 01011010_11
        let bytes = [0,0,0,0,0,0,192,90];
        let c = U64BytesToU16::new(bytes.as_slice());

        let x: Vec<_> = c.collect();

        assert_eq!(
            x,
        [23232,0,0,0]
        );

        let u = 23232;
        assert_eq!(read_bit_u16(u, 0), false);
        assert_eq!(read_bit_u16(u, 1), true);
        assert_eq!(read_bit_u16(u, 2), false);
        assert_eq!(read_bit_u16(u, 3), true);
        assert_eq!(read_bit_u16(u, 4), true);
        assert_eq!(read_bit_u16(u, 5), false);
        assert_eq!(read_bit_u16(u, 6), true);
        assert_eq!(read_bit_u16(u, 7), false);
        assert_eq!(read_bit_u16(u, 8), true);
        assert_eq!(read_bit_u16(u, 9), true);
        // println!("{:?}", c.dummy())
    }
    #[test]
    fn test_chunks_u32_to_u8(){
        let bytes = [1,2,3,4,5,6,7,8, 10,11,12,13,14,15,16,17,];
        let c = U32BytesToU8::new(bytes.as_slice());
        let x: Vec<_> = c.collect();
        assert_eq!(
            x,
            [4,3,2,1, 8,7,6,5,13,12,11,10, 17,16,15,14]
        );
    }
    #[test]
    fn test_chunks_u32_to_u16(){
        use crate::byte_decode::byte_manipulation::read_bit_u16;
        
        let bytes = [4,0,3,0,2,0,1,0];
        let c = U32BytesToU16::new(bytes.as_slice());

        let x: Vec<_> = c.collect();
        assert_eq!(
            x, 
            [3,4, 1,2]
        );

        //this encodes [7,7]: 01011010_11
        let bytes = [0,0,0,0,0,0,192,90];
        let c = U32BytesToU16::new(bytes.as_slice());
        let x: Vec<_> = c.collect();

        assert_eq!(
            x,
            [0,0,23232,0]
        );

        let u = 23232;
        assert_eq!(read_bit_u16(u, 0), false);
        assert_eq!(read_bit_u16(u, 1), true);
        assert_eq!(read_bit_u16(u, 2), false);
        assert_eq!(read_bit_u16(u, 3), true);
        assert_eq!(read_bit_u16(u, 4), true);
        assert_eq!(read_bit_u16(u, 5), false);
        assert_eq!(read_bit_u16(u, 6), true);
        assert_eq!(read_bit_u16(u, 7), false);
        assert_eq!(read_bit_u16(u, 8), true);
        assert_eq!(read_bit_u16(u, 9), true);
    }

}
