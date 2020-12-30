# Dynamic-sized lightweight bitmap

## Explanation

This zero-dependencies solution has been written with the aim to fill
the a niche of a simple and high-performance solutions
with a nice API.

## Example

```rust
use dyn_bitmap::DynBitmap;
use std::io::Write;

let source = [true, false, false].iter()
    .cycle()
    .take(256);

// You can construct bitmap from iterator with `Type = bool` or
// construct bitmap manually with `contained/1`.
//
// `DynBitmap` has high-performance `from_iter` method,
// which is preferable to `contained/1`.
let mut bitmap: DynBitmap = source.copied().collect();

// You can set value of bitmap using `set/2` function.
// It returns additional information in case of an error.
bitmap.set(true, 1).unwrap();
// You can check value of some particular bit using `get/1`.
// Note, that bit index starts from `0`.
assert_eq!(bitmap.get(1).unwrap(), true);

// You can iterate over bit values using `iter/0` function.
for (idx, value) in bitmap.iter().enumerate() {
    println!("{}: {}", idx, value);
}

let file = std::fs::File::open("foo.bin").unwrap();
// `write/1` function support writing binary bitmap representation
// to anything that implement `std::io::Write`.
bitmap.write(file).unwrap();
```
