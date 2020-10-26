# Dynamic-sized lightweight bitmap

## Example

```rust
let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
bitmap.set(0).unwrap();
assert!(bitmap.get(0).unwrap());
bitmap.clear(0).unwrap();
assert!(!bitmap.get(0).unwrap());
```
