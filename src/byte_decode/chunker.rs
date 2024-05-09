use std::io::{self, Read};

/// Turns a bytestream (R:Read) into chunks of `size`,
///  each iteratation yielding a Vec<u8>. The last chunk can be shorter than `size`
pub struct Chunks<R> {
    read: R,
    size: usize,
    hint: (usize, Option<usize>),
}

impl<R> Chunks<R> {

    /// Create a new Chunker, splitting the stream `read` into chunks of `size`
    pub fn new(read: R, size: usize) -> Self {
        Self {
            read,
            size,
            hint: (0, None),
        }
    }

    /*
    pub fn from_seek(mut read: R, size: usize) -> io::Result<Self>
    where
        R: Seek,
    {
        let old_pos = read.seek(SeekFrom::Current(0))?;
        let len = read.seek(SeekFrom::End(0))?;

        let rest = (len - old_pos) as usize; // len is always >= old_pos but they are u64
        if rest != 0 {
            read.seek(SeekFrom::Start(old_pos))?;
        }

        let min = rest / size + if rest % size != 0 { 1 } else { 0 };
        Ok(Self {
            read,
            size,
            hint: (min, None), // this could be wrong I'm unsure
        })
    }
    */

    // This could be useful if you want to try to recover from an error
    pub fn into_inner(self) -> R {
        self.read
    }
}

impl<R> Iterator for Chunks<R>
where
    R: Read,
{
    type Item = io::Result<Vec<u8>>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut chunk = Vec::with_capacity(self.size);
        match self
            .read
            .by_ref()
            .take(chunk.capacity() as u64)
            .read_to_end(&mut chunk)
        {
            Ok(n) => {
                if n != 0 {
                    Some(Ok(chunk))
                } else {
                    None
                }
            }
            Err(e) => Some(Err(e)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.hint
    }
}

/// Extending the `Read` trait whith chunking,
/// enabling it for anything that impleements `Read`
trait ReadPlus: Read {
    fn chunks(self, size: usize) -> Chunks<Self>
    where
        Self: Sized,
    {
        Chunks::new(self, size)
    }
}

impl<T: ?Sized> ReadPlus for T where T: Read {}

// fn main() -> io::Result<()> {
//     let file = std::fs::File::open("src/main.rs")?;
//     let iter = Chunks::from_seek(file, 0xFF)?; // replace with anything 0xFF was to test

//     println!("{:?}", iter.size_hint());
//     // This iterator could return Err forever be careful collect it into an Result
//     let chunks = iter.collect::<Result<Vec<_>, _>>()?;
//     println!("{:?}, {:?}", chunks.len(), chunks.capacity());

//     Ok(())
// }

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_chunk(){
        let bytes = vec![0_u8, 1, 0, 3];

        let mut c = Chunks::new(bytes.as_slice(), 2);

        assert_eq!(
            c.next().unwrap().unwrap(),
            vec![0, 1]
        );
        assert_eq!(
            c.next().unwrap().unwrap(),
            vec![0, 3]
        );
    }
}