Gapper is a optimized gap buffer implementation written in Rust.

# What is a gap buffer?

Gap buffers are mostly used in text editors, LSP's and similar applications.

In the most simple terms, a gap buffer is a dynamic array (`Vec`) with its extra capacity in the middle instead of the end.

See https://en.wikipedia.org/wiki/Gap_buffer for more information on what a gap buffer is.

# The main types

The library consists of two core types and one trait:
- GapBuf
- GapString
- Grower

## GapBuf
This is a general use gap buffer that can store any `Sized` type. In some cases a `GapBuf<char>` may be preferred when working
on a text editor or LSP.

Depending on the use case a `Grower<[T]>` can be provided to `GrowingGapBuf::with_grower` to initialize a gap buffer with your own
grow logic.

## GapString
This type is the tailored towards the common use case of a gap buffer which is storing text. 
It is guaranteed that any `&str` returned will be a valid UTF-8 encoded string. If you are working on a text editor or LSP, 
this is likely the type you care about. If the default growing mechanism isn't ideal for your use case a `Grower<str>` can be provided
to `GrowingGapString::with_grower` to initialize a gap buffer with your own grow logic.

It is essentially a `GapBuf<u8>` with convinience methods and guarantees for UTF-8 strings.

## Grower
The `Grower` trait provides a way to define your own custom grow logic for a buffer. The grower is provided slices of the left and right
side of the gap buffer allowing for more complex and stateful `Grower` implementations.

# Testing
Tests are ran with miri in order to detect undefined behavior and memory leaks. 
Most cases are covered by testing but as with any testing, it can always be improved.

Currently the tests are ran with multiple `Grower` implementations:
- DefaultGrower
- TinyGrower
- FuzzyGrower

## DefaultGrower
This is the default `Grower` provided to both types.

## TinyGrower
A `Grower` that always returns `1`, in order to simulate worse cases and off by one bugs.

## FuzzyGrower
This `Grower` returns a random integer on every call in order find bugs in edge cases.

# Performance
The implementation is highly optimized for a high number of items. To implement a high performance gap buffer `unsafe` is
basically a must in order to leave the gap uninitialized. If this isn't acceptable to you feel free to use a different, 
safer but slower gap buffer implementation.
