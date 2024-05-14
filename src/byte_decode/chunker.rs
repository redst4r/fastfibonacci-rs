//!
use std::io::ErrorKind;
use std::io::Read;
use byteorder::LittleEndian;
use byteorder::BigEndian;
use byteorder::ReadBytesExt;
use crate::byte_decode::byte_manipulation::read_bit_u32;

/// Turns a bytestream into a stream of U64s
/// assumes little endian bytestream.
/// 
/// Note, if the stream is NOT a multiple of 8bytes, it'll drop the remainder!
pub struct U64BytesToU64<R> {
    read: R,
}

impl<R:Read> U64BytesToU64<R> {
    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self {
            read,

        }
    }
    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        self.read
    }
}
impl<R:Read> Iterator for U64BytesToU64<R>
{
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

#[cfg(test)]
mod test2 {
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
}

/// Turns a bytestream (R:Read) into chunks of `size`,
///  each iteratation yielding a Vec<u8>. The last chunk can be shorter than `size`
// pub struct Chunks<R> {
//     read: R,
//     size: usize,
//     hint: (usize, Option<usize>),
// }

// impl<R> Chunks<R> {

//     /// Create a new Chunker, splitting the stream `read` into chunks of `size`
//     pub fn new(read: R, size: usize) -> Self {
//         Self {
//             read,
//             size,
//             hint: (0, None),
//         }
//     }

//     // This could be useful if you want to try to recover from an error
//     pub fn into_inner(self) -> R {
//         self.read
//     }
// }

// impl<R:Read> Iterator for Chunks<R>
// {
//     type Item = io::Result<Vec<u8>>;

//     fn next(&mut self) -> Option<Self::Item> {
//         let mut chunk = Vec::with_capacity(self.size);
//         match self.read
//             .by_ref()
//             .take(chunk.capacity() as u64)
//             .read_to_end(&mut chunk)
//         {
//             Ok(n) => {
//                 if n != 0 {
//                     Some(Ok(chunk))
//                 } else {
//                     None
//                 }
//             }
//             Err(e) => Some(Err(e)),
//         }
//     }

//     fn size_hint(&self) -> (usize, Option<usize>) {
//         self.hint
//     }
// }

// /// Extending the `Read` trait whith chunking,
// /// enabling it for anything that impleements `Read`
// trait ReadPlus: Read {
//     fn chunks(self, size: usize) -> Chunks<Self>
//     where
//         Self: Sized,
//     {
//         Chunks::new(self, size)
//     }
// }

// impl<T: ?Sized> ReadPlus for T where T: Read {}

// #[cfg(test)]
// mod test {
//     use super::*;
//     #[test]
//     fn test_chunk(){
//         let bytes = vec![0_u8, 1, 0, 3];

//         let mut c = Chunks::new(bytes.as_slice(), 2);

//         assert_eq!(
//             c.next().unwrap().unwrap(),
//             vec![0, 1]
//         );
//         assert_eq!(
//             c.next().unwrap().unwrap(),
//             vec![0, 3]
//         );
//     }
// }

/// Consumes a bytestream (groups of 8, from u64s), returning it ready for FastFibnoacci decoding
/// in 1byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U64BytesToU8<R> {
    read: R,
    // each u64 will creatye a u8, but we emit them one by one
    // buf: Vec<u8>
}

impl<R:Read> U64BytesToU8<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read,}
            // buf: Vec::with_capacity(8)}
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        // assert!(self.buf.is_empty());
        self.read
    }
}


impl<R:Read> Iterator for U64BytesToU8<R>
{
    type Item = [u8;8];
    fn next(&mut self) -> Option<Self::Item> {
        // to proper way: load as little endian,
        // then invert 
        let u = self.read.read_u64::<LittleEndian>();

        match u {
            Ok(n) => {
                let reversed_bytes = n.to_be_bytes();
                Some(reversed_bytes)
            },
            Err(e) => {
                match e.kind() {
                    ErrorKind::UnexpectedEof => None,
                    _ => panic!("io error"),
                }
            }
        }
    }
}

#[test]
fn test_chunks_u64_to_u8(){
    let bytes = [1,2,3,4,5,6,7,8, 10,11,12,13,14,15,16,17,];
    let mut c = U64BytesToU8::new(bytes.as_slice());
    assert_eq!(
        c.next(),
        Some([8,7,6,5,4,3,2,1])
    );
    assert_eq!(
        c.next(),
        Some([17,16,15,14,13,12,11,10])
    );
}



/// Consumes a bytestream, returning it ready for FastFibnoacci decoding
/// in 2byte segments
/// (due to the way things work with Endianess, it essentially revserses each 8byte chunk)
pub struct U64BytesToU16<R> {
    read: R,
}

impl<R:Read> U64BytesToU16<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self {
            read,
        }
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        self.read
    }
}


impl<R> Iterator for U64BytesToU16<R>
where
    R: Read,
{
    type Item = [u16;4];

    fn next(&mut self) -> Option<Self::Item> {

        // to proper way: load as little endian,
        // then invert 
        let u = self.read.read_u64::<LittleEndian>();

        match u {
            Ok(n) => {
                let reversed_bytes = n.to_be_bytes();
                let mut buf = [0_u16; 4];
                reversed_bytes.as_slice().read_u16_into::<BigEndian>(&mut buf).unwrap();
                Some(buf)
            },
            Err(e) => {
                match e.kind() {
                    ErrorKind::UnexpectedEof => None,
                    _ => panic!("io error"),
                }
            },
        }
    }
}



#[test]
fn test_chunks_u64_to_u16(){
    use crate::byte_decode::byte_manipulation::read_bit_u16;
    
    let bytes = [4,0,3,0,2,0,1,0];
    let mut c = U64BytesToU16::new(bytes.as_slice());

    assert_eq!(
        c.next(),
        Some([1,2,3,4])
    );

    //this encodes [7,7]: 01011010_11
    let bytes = [0,0,0,0,0,0,192,90];
    let mut c = U64BytesToU16::new(bytes.as_slice());

    assert_eq!(
        c.next(),
        Some([23232,0,0,0])
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


///
pub struct U64BytesToU32<R> {
    read: R,
    // each u64 will creatye a u8, but we emit them one by one
    // buf: Vec<u8>
}

impl<R:Read> U64BytesToU32<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R) -> Self {
        Self { read,}
            // buf: Vec::with_capacity(8)}
    }

    /// This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        // assert!(self.buf.is_empty());
        self.read
    }
}


impl<R:Read> Iterator for U64BytesToU32<R>
{
    type Item = [u32;2];
    fn next(&mut self) -> Option<Self::Item> {
        // to proper way: load as little endian,
        // then invert 
        let u = self.read.read_u64::<LittleEndian>();

        match u {
            Ok(n) => {
                let reversed_bytes = n.to_be_bytes();
                let mut buf = [0_u32; 2];
                reversed_bytes.as_slice().read_u32_into::<BigEndian>(&mut buf).unwrap();
                Some(buf)
            },
            Err(e) => {
                match e.kind() {
                    ErrorKind::UnexpectedEof => None,
                    _ => panic!("io error"),
                }
            }
        }
    }
}

#[test]
fn test_chunks_u64_to_u32(){    
    let bytes = [4,0,3,0,2,0,1,0];
    let mut c = U64BytesToU32::new(bytes.as_slice());

    assert_eq!(
        c.next(),
        Some([65538, 196612])
    );

    //this encodes [7,7]: 01011010_11
    let bytes = [0,0,0,0,0,0,192,90];
    let mut c = U64BytesToU32::new(bytes.as_slice());

    assert_eq!(
        c.next(),
        Some([1522532352,0])
    );

    let u = 1522532352;
    assert_eq!(read_bit_u32(u, 0), false);
    assert_eq!(read_bit_u32(u, 1), true);
    assert_eq!(read_bit_u32(u, 2), false);
    assert_eq!(read_bit_u32(u, 3), true);
    assert_eq!(read_bit_u32(u, 4), true);
    assert_eq!(read_bit_u32(u, 5), false);
    assert_eq!(read_bit_u32(u, 6), true);
    assert_eq!(read_bit_u32(u, 7), false);
    assert_eq!(read_bit_u32(u, 8), true);
    assert_eq!(read_bit_u32(u, 9), true);
    // println!("{:?}", c.dummy())
}
