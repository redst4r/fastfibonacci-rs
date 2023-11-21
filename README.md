# FastFibonacci

Rust library implementing the [FastFibonacci](https://ceur-ws.org/Vol-567/paper14.pdf) integer compression/decompression algorithm. Besides, the crate also supplies regular fibonacci compression/decompression.

## Introduction
[Fibonacci encoding](https://en.wikipedia.org/wiki/Fibonacci_coding) is a variable-length encoding of integers, with the special property that any encoding of an interger ends in `1` (binary) and no encoding contains `11`. Hence one can use `11` as a separator in a stream of Fibonacci encoded integers.

Regular Fibonacci decoding works decoding bit by bit, which can be quite slow. [FastFibonacci](https://ceur-ws.org/Vol-567/paper14.pdf) decoding looks at `n` bits at once, decoding this chunk in a single operation which can be faster.


## Performance
Regular Fibonacci encoding is up to speed with other rust implementations, e.g. [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate (which I took some code from):
- Fibonacci encoding: 
    - this crate: 75ms/ 1M integers 
    - fibonnaci_codec: 88ms / 1M integers

Regular fibonacci decoding (iterator based) is up to speed with the [fibonnaci_codec](https://crates.io/crates/fibonacci_codec) crate. 
The **FastFibonacci** decoding functions are ~2x faster, but have some constant overhead  (i.e. only pays of when decoding *many* integers):
- Fibonacci decoding: 
    - regular decoding: 92ms/ 1M integers
    - fibonnaci_codec: 108ms / 1M integers
    - fast decoding (u8 segments): 40ms / 1M integers
    - fast decoding (u16 segments): 30ms / 1M integers
    - fast decoding (using an iterator): 54ms / 1M integers


## Examples
Regular encoding and decoding:
```rust
use fastfibonacci::fibonacci::{encode, decode, FibonacciDecoder};
let encoded = encode(&vec![34, 12]) ;

// Decoding
let decoded = decode(&encoded, false); // 2nd argument: shift all values by -1 (in case we wanted to encode 0 in the fibonacci encoding)
assert_eq!(decoded, vec![34,12]);

// Alternatively, we can also create an iterator (yields one decoded int at a time)
let f = FibonacciDecoder::new(&encoded, false);
assert_eq!(f.collect::<Vec<_>>(), vec![34,12])
```

Fast decoding:
```rust
use fastfibonacci::fast::{fast_decode, LookupU8Vec, LookupU16Vec };
use bitvec::prelude as bv;
let bits = bv::bits![u8, bv::Msb0; 
    1,0,1,1,0,1,0,1,
    1,0,1,0,0,1,0,1,
    0,1,1,1,0,0,1,0].to_bitvec();
// using a u8 lookup table
let table: LookupVec<u8> = LookupVec::new();
let r = fast_decode(&bits, &table);
assert_eq!(r, vec![4,7, 86]);

// using a u16 table
let table: LookupVec<u16> = LookupVec::new();
let r = fast_decode(&bits, &table);
assert_eq!(r, vec![4,7, 86]);
```