use std::{backtrace, collections::VecDeque, io::{self, BufReader, Read}};

use crate::{bare_metal::Dirty8, bare_metal_64::Dirty64};

/// Turns a stream of u8 into a stream of u64
struct U64Reader<R: io::BufRead> {
    inner: R,
}

impl<R: io::BufRead> U64Reader<R> {
    pub fn new(inner: R) -> Self {
        Self {
            inner
        }
    }

	pub fn pop_inner(self) -> R{
		self.inner
	}

	fn get_inner(&mut self) -> &mut R {
		&mut self.inner
	}
}

impl<R: io::BufRead> Iterator for U64Reader<R> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buff: [u8; 8] = [0;8];
        self.inner.read_exact(&mut buff).ok()?; // careful, this convert any ioError (not able to fill the buffer) into a `None`
        Some(u64::from_be_bytes(buff))
    }
}

#[test]
fn test_U64iter() {
	let x = vec![1_u8, 2,3,4,5,6,7,8];

	let r = BufReader::new(x.as_slice());
	let ur = U64Reader::new(r);

	let u64_vec= ur.collect::<Vec<u64>>();
	assert_eq!(u64_vec.len(), 1);
	assert_eq!(u64_vec, vec![72623859790382856]);
	println!("{:?}", u64_vec)
}

/// make sure that the trailing bytes (if the stream isnt an exact multiple of 8*bytes)
/// are recovered
#[test]
fn test_U64iter_trailing() {
	let x = vec![
        1_u8, 2,3,4,5,6,7,8,  //u64
        9,10  // additional bytes
    ];

	let r = BufReader::new(x.as_slice());
	let mut ur = U64Reader::new(r);

	assert_eq!(ur.next(), Some(72623859790382856));
	
    // get the inner part
	let inner = ur.pop_inner();
	
	let mut remainder = Vec::new();
	for b in inner.bytes() {
		match  b {
			Ok(some_byte) => {remainder.push(some_byte)},
			Err(_) => {panic!("error")},
		}
	}
	assert_eq!(remainder, vec![9, 10])
}

/// test the behavior when asking for another u64
/// when infact theres less than 8bytes in the stream
#[test]
fn test_U64iter_not_enough_bytes() {
	let x = vec![
        1_u8, 2,3,4,5,6,7,8,  //u64
        9,10  // additional bytes
    ];

	let r = BufReader::new(x.as_slice());
	let mut ur = U64Reader::new(r);

	assert_eq!(ur.next(), Some(72623859790382856));
	

    assert_eq!(None, ur.next());

    // retrieve the missing bytes
	let inner = ur.pop_inner();
	let mut remainder = Vec::new();
	for b in inner.bytes() {
		match  b {
			Ok(some_byte) => {remainder.push(some_byte)},
			Err(_) => {panic!("error")},
		}
	}
	assert_eq!(remainder, vec![9, 10])    

}


/// iterates over a byte stream, preferentially yieling u64
/// but if there's not enough bytes to from a u64, yield bytes one bye one
struct U64U8Reader<R: io::BufRead> {
    inner: R,
    tbuffer: [u8; 8], // where we store the results of inner.read
    u8buffer: VecDeque<u8>, //whenever we run into a not complete u64, we need to yield it byte by byte
}

impl<R: io::BufRead> U64U8Reader<R> {
    pub fn new(inner: R) -> Self {
        let tbuffer = [0_u8;8];
        let u8buffer: VecDeque<u8> = VecDeque::new();
        Self {
            inner, tbuffer, u8buffer
        }
    }

	pub fn pop_inner(self) -> R{
		self.inner
	}

	fn get_inner(&mut self) -> &mut R {
		&mut self.inner
	}
}

#[derive(Debug, Eq, PartialEq)]
pub enum Element {
    U64(u64),
    U8(u8)
}
impl<R: io::BufRead> Iterator for U64U8Reader<R> {
    type Item = Element;

    fn next(&mut self) -> Option<Self::Item> {

        // in case there's any u8 to yield
        if self.u8buffer.len() > 0 {
            let el = self.u8buffer.pop_front().unwrap();
            return Some(Element::U8(el));
        }

		match self.inner.read(&mut self.tbuffer) {
            Ok(0) => {
                // cant get any more bytes
                return None
            }
            Ok(8) => {
				println!("8 bytes");
				// got 8 bytes, turn into u64 and add to buffer
				let el = u64::from_be_bytes(self.tbuffer);
                return Some(Element::U64(el));
			},
			Ok(n) => {
				println!("{n} bytes");
                // tbuffer[..n] is populated
                let el = self.tbuffer[0];
                for i in 1..n {
                    self.u8buffer.push_back(self.tbuffer[i])
                }
                return Some(Element::U8(el));
			}
			Err(_) => todo!(),
		}
    }
}

#[test]
fn test_U64U8Reader_iter() {
	let x = vec![
        1_u8, 2,3,4,5,6,7,8,
        1_u8, 2,3,4,5,6,7,8,
        9, 10 // two additional bytes
    ];

	let r = BufReader::new(x.as_slice());
	let mut ur = U64U8Reader::new(r);

    assert_eq!(
        ur.next(),
        Some(Element::U64(72623859790382856))
    );
    
    assert_eq!(
        ur.next(),
        Some(Element::U64(72623859790382856))
    );
    assert_eq!(
        ur.next(),
        Some(Element::U8(9))
    );
    assert_eq!(
        ur.next(),
        Some(Element::U8(10))
    );    

    assert_eq!(
        ur.next(),
        None
    );    
}


/// pull a few u64s of the stream, than turn into retular bytestream
/// make sure those bytes are still in there
#[test]
fn test_U64U8Reader_continue_normal_stream() {
	let x = vec![
        1_u8, 2,3,4,5,6,7,8,
        1_u8, 2,3,4,5,6,7,8,
        9, 10 // two additional bytes
    ];

	let r = BufReader::new(x.as_slice());
	let mut ur = U64U8Reader::new(r);

    assert_eq!(
        ur.next(),
        Some(Element::U64(72623859790382856))
    );
    
    assert_eq!(
        ur.next(),
        Some(Element::U64(72623859790382856))
    );

    // convert back
    let mut buf = [0;2];
    let mut inner = ur.pop_inner();
    inner.read_exact(&mut buf).unwrap();

    assert_eq!(
        buf.to_vec(),
        vec![9,10]
    );
}


struct FullIter <R: io::BufRead + 'static> {
    stream: U64U8Reader<R>,

    u64decoder: Dirty64<'static>,
    u8decoder: Dirty8<'static>,


}