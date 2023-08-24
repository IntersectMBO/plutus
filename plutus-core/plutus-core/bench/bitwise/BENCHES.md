# Benchmarks of bitwise operations for Plutus core

## Introduction

## Conventions

We use _kilobyte_ (_KiB_ for short) to mean $2^{10}$ (1024) bytes.

We assume versions of Haskell libraries as defined by Plutus and determined by
`cabal new-freeze`. In particular, the following library versions are assumed to
be in use:

* `bytestring-0.10.12.0`
* `wide-word-0.1.1.2`

An operation is _bit-parallel_ if it treats its inputs as vectors of bits and
assumes no other structure. For example [bitwise logical
AND](https://en.wikipedia.org/wiki/Bitwise_operation#AND) is bit-parallel, while
a [bitwise
rotation](https://en.wikipedia.org/wiki/Bitwise_operation#Circular_shift) isn't.
This extends the definition of right-to-left computability defined in [Hacker's
Delight](https://en.wikipedia.org/wiki/Hacker%27s_Delight), but is stricter.

We use _population count_ to mean the number of 1 bits. We use this term with
individual bytes, words, or sequences of either.

## Background

Plutus Core, which is designed to be executed on-chain, has unusual limitations
regarding performance. Specifically, the size of its possible arguments is
_significantly_ bounded: according to
[CIP-0009](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0009), the
current on-chain transaction size limit is 16384 bytes (16KiB), which includes
both script sources and arguments. While this limit could rise in the future,
currently, it means that `ByteString` arguments larger than about 2KiB aren't
practical. This implies that:

* Asymptotically-optimal solutions may not be worthwhile if their 'ramp-up'
  requires inputs approaching, or larger than, 2KiB; and
* Small inputs must be considered the norm.

### Spatial and temporal locality

## Implementation

### Bitwise binary operations

The naive approach (and our first) uses a combination of `fromListN` and `zip` 
together with the operator in question; in essence, this streams both arguments 
into a list of `Word8`s, combines them with the given operator, then 'repacks' 
into a `ByteString`. This approach, while easy to implement, is likely to be 
fairly slow once the size of its arguments becomes even moderately large. We 
enumerate the reasons for this hypothesis below; many of these are based on the 
reasoning described in [the spatial and temporal locality](#spatial-and-temporal-locality) 
section.

* The `ByteString` library 
  [does not use the size hint](https://hackage.haskell.org/package/bytestring-0.10.12.0/docs/src/Data.ByteString.Internal.html#line-194) 
  given to `fromListN`. This requires a traversal of the input list, which
  forces it, making any stream fusion from GHC ineffective.
* Haskell linked lists lack spatial locality, and due to the above, we have to
  force spatially local data into a spatially non-local form, only to then
  immediately convert it _back_ to a spatially local form again. This not only
  requires copying the data, it also means that we lose the benefits of spatial
  locality for no reason.
* Haskell linked lists full of `Word8` lack temporal locality: even though a
  modern machine can fit eight `Word8`s into a single register, if the data is
  in a list, this cannot be done.

These concerns were seen as sufficient to warrant the introduction of
`packZipWith`, which [avoids creating an intermediate list](https://github.com/haskell/bytestring/pull/295). 
This operation amounts to creating an empty `ByteString` of the right length,
then performing the 'zipping' in-place. This avoids the problems of spatial
locality, and in theory could also avoid problems of temporal locality if the
operation being performed is bit-parallel. However, in general, 'zipping'
operations on `Word8`s cannot be assumed to be bit-parallel, which requires a
more conservative, 'byte-at-a-time' approach. Furthermore, `packZipWith` only
became available in the `bytestring` library as of [release
0.11.1.0](https://hackage.haskell.org/package/bytestring-0.11.1.0/changelog).
Thus, we replicate it for our second approach.

All of our bitwise binary operations are bit-parallel by their definition; this
allows an implementation where we exploit temporal locality to process eight
bytes at a time. This essentially mirrors what the second approach does, but
instead first takes a maximal number of 'big steps' (eight bytes at a time),
followed by any remaining inputs being processed one byte at a time. We take
this as our third approach. We also attempt a fourth approach, where we take
even larger steps, using the `Word256` type from `wide-word`: this amounts to a
four-way [loop unroll](https://en.wikipedia.org/wiki/Loop_unrolling), as GHC
cannot currently generate SIMD instructions, even for bit-parallel operations.
This can, in theory, still be beneficial, due to
[ILP](https://en.wikipedia.org/wiki/Instruction-level_parallelism) being
available on most modern CPUs. More specifically, the third approach works as
follows:

1. Allocate an empty `ByteString` of the correct length.
2. While at least eight bytes of both inputs are remaining, perform the bitwise
   operation on an eight-byte chunk of both inputs, then write the result to the
   corresponding part of the empty `ByteString` from 1.
3. For the remaining bytes, perform the bitwise operation on each of the
   corresponding bytes of the input, writing them to the empty `ByteString` from
   1.

The fourth approach works as follows:

1. Allocate an empty `ByteString` of the correct length.
2. While at least 32 bytes of both inputs are remaining, perform the bitwise
   operation on a 32-byte chunk of both inputs, then write the result to the
   corresponding part of the empty `ByteString` from 1.
3. While at least eight bytes of both inputs are remaining, perform the bitwise
   operation on an eight-byte chunk of both inputs, then write the result to the
   corresponding part of the empty `ByteString` from 1.
4. For the remaining bytes, perform the bitwise operation on each of the
   corresponding bytes of the input, writing them to the empty `ByteString` from
   1.

### Bitwise complement

A naive (and our first) approach would use `map` from `bytestring`: this is
implemented as a [loop over a preconstructed empty
`bytestring`](https://hackage.haskell.org/package/bytestring-0.10.12.0/docs/src/Data.ByteString.html#map),
and thus has good spatial locality. In theory, if given a bit-parallel
operation, it could make use of temporal locality by operating on larger widths
(such as whole machine words), but as `Word8` operations cannot be assumed to be
bit-parallel in general, it must work 'byte-at-a-time'. In our case, bitwise
complement _is_ bit-parallel, so our second approach attempts to make use of
this fact, essentially doing the following:

1. Allocate an empty `ByteString` the same length as the input.
2. While at least eight bytes of the input remains, determine the bitwise
   complement of an eight-byte chunk of the input, then write it to the
   corresponding part of the empty `ByteString` from 1.
3. For the remaining bytes, perfor the bitwise complement on each of the
   corresponding bytes of the input, writing them to the empty `ByteString` from
   1.

We also define a third approach which takes even larger steps, using the
`Word256` type from `wide-word`. This amounts to a four-way loop unroll, as GHC
cannot currently generate SIMD instructions, even for bit-parallel operations.
This can, in theory, still be beneficial, due to ILP being available on most
modern CPUs. More specifically, the third approach works as follows:

1. Allocate an empty `ByteString` the same length as the input.
2. While at least 32 bytes of of the input remains, determine the bitwise
   complement of a 32-byte chunk of the input, then write it to the
   corresponding part of the empty `ByteString` from 1.
3. While at least eight bytes of the input remains, determine the bitwise
   complement of an eight-byte chunk of the input, then write it to the
   corresponding part of the empty `ByteString` from 1.
4. For the remaining bytes, perfor the bitwise complement on each of the
   corresponding bytes of the input, writing them to the empty `ByteString` from
   1.

### Population count

A naive approach would involve a fold over the `Word8`s in the argument, summing
the result of `popCount`. This forms our first approach, using the `foldl'`
function provided by `bytestring`. This approach makes good use of spatial
locality, but not particularly good use of temporal locality: each `Word8` we
load into a register to population count still requires a memory transfer, but
we only population count 8 bits, rather than the 64 bits that could fit into the
register. Moreover, x86_64 platforms have efficient instructions dedicated to
population counting, which can easily count a whole register's worth of bits.
Thu, our second approach makes use of this capability by doing two 'phases' of
counting: firstly, we count eight-byte chunks, then finish what remains one byte
at a time. Specifically, we do the following:

1. Initialize a counter to 0.
2. While at least eight bytes of the input remains, population count an
   eight-byte chunk, then add the result to the counter.
3. While any bytes of the input remain, population count one byte, then add the
   result to the counter.
4. Return the counter.

We also define a third approach which takes even larger chunks, using the
`Word256` type from `wide-word`. This amounts to a four-way loop unroll, as
there are no specialized instructions for population counting chunks larger than
eight bytes on any current architectures supported by GHC. This can, in theory,
still be beneficial, due to ILP being available on most modern CPUs. More
specifically, the third approach works as follows:

1. Initialize a counter to 0.
2. While at least 32 bytes of input remains, population count a 32-byte chunk,
   then add the result to the counter.
3. While at least eight bytes of the input remains, population count an
   eight-byte chunk, then add the result to the counter.
4. While any bytes of the input remain, population count one byte, then add the
   result to the counter.
5. Return the counter.

## Methodology

### Bitwise binary operations

We benchmark only bitwise AND, as the other operations do not differ
structurally, are also bit-parallel, and given a fixed width of inputs, are
constant time relative that width. We implement all four approaches; for the
third and fourth approaches, we implement them both in Haskell and in C, which
is called via the FFI. This allows us to see if any overheads are being
introduced by GHC.

We use pairs of inputs of the following lengths:

* 1
* 3
* 7
* 15
* 31
* 63
* 127
* 255
* 511
* 1023
* 2047

We choose these values to disadvantage the third and fourth approaches as much
as possible, as values that are one less than a power of 2 in length would
require them to do the most work in their last step.

We compare all approaches to the first (that is, naive) one.

### Bitwise complement

We implement all three approaches; for the second approach, we implement it both
in Haskell and in C, which is called via the FFI. This is to determine whether
any overheads are being introduced by GHC.

We use inputs of the following lengths:

* 1
* 3
* 7
* 15
* 31
* 63
* 127
* 255
* 511
* 1023
* 2047

We choose these values to disadvantage the second and third approaches as much
as possible, as values that are one less than a power of 2 in length would
require them to do the most work in their last step.

We compare all approaches to the first (that is, naive) one.

### Population count

We implement all three approaches. We use inputs of the following lengths:

* 1
* 3
* 7
* 15
* 31
* 63
* 127
* 255
* 511
* 1023
* 2047

We choose these values to disadvantage the second and third approaches as much
as possible, as values that are one less than a power of 2 in length would
require them to do the most work in their second-to-last step.

## Results

Throughout, we run benchmarks (implemented with `tasty-bench`) with `--stdev=1
--timeout=200` to ensure minimal interference and accurate readings, while
avoiding timeouts due to the increased time required to get accurate readings.

### Bitwise binary operations

The results of our benchmarks given the methodology we described are below.
Throughout, `zipWith` refers to the first approach, `packZipWith` to the second
approach, `chunkedZipWith (2 blocks)` to the third approach, and `chunkedZipWith
(3 blocks)` to the fourth approach. We also mark the C implementations of the
third and fourth approach. All multipliers are shows as multiples of the running
time of the first approach on the same length of data.

```
All
  Bitwise AND
    Bitwise AND, length 1
      zipWith:                      OK (0.86s)
        46.2 ns ± 864 ps, 254 B  allocated,   0 B  copied,  45 MB peak memory
      packZipWith:                  OK (5.96s)
        177  ns ± 2.3 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.83x
      chunkedZipWith (2 blocks):    OK (6.00s)
        178  ns ± 1.0 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.85x
      chunkedZipWith (2 blocks, C): OK (12.14s)
        180  ns ± 904 ps, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.89x
      chunkedZipWith (3 blocks):    OK (3.15s)
        184  ns ± 2.1 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 3.99x
      chunkedZipWith (3 blocks, C): OK (0.78s)
        180  ns ± 3.5 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 3.90x
    Bitwise AND, length 3
      zipWith:                      OK (1.85s)
        54.3 ns ± 530 ps, 350 B  allocated,   0 B  copied,  52 MB peak memory
      packZipWith:                  OK (0.78s)
        181  ns ± 3.2 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 3.33x
      chunkedZipWith (2 blocks):    OK (6.28s)
        186  ns ± 1.3 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.43x
      chunkedZipWith (2 blocks, C): OK (0.79s)
        184  ns ± 3.5 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 3.39x
      chunkedZipWith (3 blocks):    OK (6.39s)
        189  ns ± 3.7 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.47x
      chunkedZipWith (3 blocks, C): OK (100.97s)
        187  ns ± 3.1 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 3.45x
    Bitwise AND, length 7
      zipWith:                      OK (1.18s)
        68.2 ns ± 1.0 ns, 508 B  allocated,   0 B  copied,  52 MB peak memory
      packZipWith:                  OK (0.78s)
        182  ns ± 3.2 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 2.67x
      chunkedZipWith (2 blocks):    OK (3.25s)
        191  ns ± 942 ps, 358 B  allocated,  95 B  copied,  52 MB peak memory, 2.80x
      chunkedZipWith (2 blocks, C): OK (3.17s)
        188  ns ± 1.2 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 2.75x
      chunkedZipWith (3 blocks):    OK (3.27s)
        194  ns ± 966 ps, 358 B  allocated,  95 B  copied,  52 MB peak memory, 2.85x
      chunkedZipWith (3 blocks, C): OK (3.28s)
        193  ns ± 2.4 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 2.83x
    Bitwise AND, length 15
      zipWith:                      OK (0.91s)
        106  ns ± 1.7 ns, 844 B  allocated,   0 B  copied,  52 MB peak memory
      packZipWith:                  OK (3.23s)
        191  ns ± 2.7 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 1.80x
      chunkedZipWith (2 blocks):    OK (1.68s)
        198  ns ± 3.4 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 1.87x
      chunkedZipWith (2 blocks, C): OK (1.69s)
        196  ns ± 2.6 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 1.85x
      chunkedZipWith (3 blocks):    OK (13.48s)
        201  ns ± 1.2 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 1.90x
      chunkedZipWith (3 blocks, C): OK (3.40s)
        200  ns ± 1.2 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 1.88x
    Bitwise AND, length 31
      zipWith:                      OK (1.69s)
        199  ns ± 1.9 ns, 1.5 KB allocated,   0 B  copied,  52 MB peak memory
      packZipWith:                  OK (6.10s)
        182  ns ± 1.4 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.91x
      chunkedZipWith (2 blocks):    OK (3.15s)
        186  ns ± 2.0 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.93x
      chunkedZipWith (2 blocks, C): OK (0.80s)
        184  ns ± 3.4 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.92x
      chunkedZipWith (3 blocks):    OK (6.55s)
        194  ns ± 1.6 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.97x
      chunkedZipWith (3 blocks, C): OK (3.28s)
        194  ns ± 3.4 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.97x
    Bitwise AND, length 63
      zipWith:                      OK (0.79s)
        371  ns ± 6.4 ns, 2.8 KB allocated,   0 B  copied,  52 MB peak memory
      packZipWith:                  OK (7.81s)
        233  ns ± 918 ps, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.63x
      chunkedZipWith (2 blocks):    OK (3.84s)
        228  ns ± 2.2 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.61x
      chunkedZipWith (2 blocks, C): OK (0.93s)
        215  ns ± 3.2 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.58x
      chunkedZipWith (3 blocks):    OK (3.84s)
        226  ns ± 2.7 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.61x
      chunkedZipWith (3 blocks, C): OK (0.96s)
        223  ns ± 3.5 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.60x
    Bitwise AND, length 127
      zipWith:                      OK (1.43s)
        665  ns ±  11 ns, 5.4 KB allocated,   1 B  copied,  52 MB peak memory
      packZipWith:                  OK (0.91s)
        209  ns ± 3.8 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.31x
      chunkedZipWith (2 blocks):    OK (0.82s)
        181  ns ± 2.8 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.27x
      chunkedZipWith (2 blocks, C): OK (52.40s)
        196  ns ± 2.6 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.29x
      chunkedZipWith (3 blocks):    OK (0.87s)
        191  ns ± 3.0 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.29x
      chunkedZipWith (3 blocks, C): OK (3.26s)
        190  ns ± 2.6 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.29x
    Bitwise AND, length 255
      zipWith:                      OK (0.75s)
        1.38 μs ±  22 ns,  11 KB allocated,   3 B  copied,  52 MB peak memory
      packZipWith:                  OK (4.49s)
        263  ns ± 898 ps, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.19x
      chunkedZipWith (2 blocks):    OK (1.77s)
        204  ns ± 3.5 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.15x
      chunkedZipWith (2 blocks, C): OK (1.81s)
        208  ns ± 3.6 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.15x
      chunkedZipWith (3 blocks):    OK (14.16s)
        210  ns ± 940 ps, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.15x
      chunkedZipWith (3 blocks, C): OK (3.41s)
        197  ns ± 2.1 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.14x
    Bitwise AND, length 511
      zipWith:                      OK (1.42s)
        2.67 μs ±  43 ns,  21 KB allocated,   2 B  copied,  52 MB peak memory
      packZipWith:                  OK (1.48s)
        332  ns ± 3.1 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.12x
      chunkedZipWith (2 blocks):    OK (1.94s)
        219  ns ± 3.0 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.08x
      chunkedZipWith (2 blocks, C): OK (3.74s)
        217  ns ± 2.2 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.08x
      chunkedZipWith (3 blocks):    OK (1.04s)
        230  ns ± 2.7 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.09x
      chunkedZipWith (3 blocks, C): OK (1.90s)
        214  ns ± 2.9 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.08x
    Bitwise AND, length 1023
      zipWith:                      OK (0.78s)
        5.68 μs ± 100 ns,  42 KB allocated,  55 B  copied,  52 MB peak memory
      packZipWith:                  OK (1.13s)
        499  ns ± 7.9 ns, 341 B  allocated,  91 B  copied,  52 MB peak memory, 0.09x
      chunkedZipWith (2 blocks):    OK (1.28s)
        282  ns ± 3.7 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.05x
      chunkedZipWith (2 blocks, C): OK (1.29s)
        280  ns ± 3.9 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.05x
      chunkedZipWith (3 blocks):    OK (1.38s)
        297  ns ± 4.7 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.05x
      chunkedZipWith (3 blocks, C): OK (1.29s)
        283  ns ± 3.2 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.05x
    Bitwise AND, length 2047
      zipWith:                      OK (0.78s)
        11.2 μs ± 170 ns,  85 KB allocated,  88 B  copied,  52 MB peak memory
      packZipWith:                  OK (3.50s)
        798  ns ± 4.1 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.07x
      chunkedZipWith (2 blocks):    OK (1.76s)
        385  ns ± 3.5 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.03x
      chunkedZipWith (2 blocks, C): OK (6.57s)
        379  ns ± 1.6 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.03x
      chunkedZipWith (3 blocks):    OK (1.88s)
        414  ns ± 4.8 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.04x
      chunkedZipWith (3 blocks, C): OK (1.78s)
        395  ns ± 3.1 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.04x
```

We observe that, up to length 15, the first approach comes out ahead, especially
on smaller inputs. However, at around length 30, a 'phase transition' occurs,
where the other approaches win out, with this becoming increasingly apparent as
we get to the limits of our sizes. In particular, in the middle of the size
range (between 63 and 511 bytes inclusive), other approaches beat out the naive
one by a factor of between 2 and 10, which is not insignificant. We also note
that the first approach allocates substantially more than the others, likely due
to lists it cannot fuse away; all other approaches have fixed allocations.

It is not clear from the above whether the second, third or fourth approaches
are better in general; to this end, we ran only these in isolation, comparing
the third and fourth approaches to the second:

```
All
  Packed bitwise AND
    Packed bitwise AND, length 31
      packZipWith:                  OK (3.34s)
        390  ns ± 2.8 ns, 3.0 KB allocated,   0 B  copied,  45 MB peak memory
      chunkedZipWith (2 blocks):    OK (6.21s)
        184  ns ± 2.7 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.47x
      chunkedZipWith (2 blocks, C): OK (1.57s)
        184  ns ± 1.5 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.47x
      chunkedZipWith (3 blocks):    OK (3.20s)
        189  ns ± 1.7 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.48x
      chunkedZipWith (3 blocks, C): OK (1.62s)
        190  ns ± 2.8 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.49x
    Packed bitwise AND, length 63
      packZipWith:                  OK (0.74s)
        679  ns ±  12 ns, 5.8 KB allocated,   0 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (6.91s)
        208  ns ± 2.2 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.31x
      chunkedZipWith (2 blocks, C): OK (3.93s)
        236  ns ± 1.3 ns, 430 B  allocated,  95 B  copied,  52 MB peak memory, 0.35x
      chunkedZipWith (3 blocks):    OK (8.05s)
        239  ns ± 796 ps, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.35x
      chunkedZipWith (3 blocks, C): OK (8.10s)
        242  ns ± 2.2 ns, 431 B  allocated,  95 B  copied,  52 MB peak memory, 0.36x
    Packed bitwise AND, length 127
      packZipWith:                  OK (0.73s)
        1.40 μs ±  22 ns,  11 KB allocated,   1 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (50.76s)
        188  ns ± 2.6 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.13x
      chunkedZipWith (2 blocks, C): OK (1.67s)
        191  ns ± 2.4 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.14x
      chunkedZipWith (3 blocks):    OK (0.84s)
        193  ns ± 3.5 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.14x
      chunkedZipWith (3 blocks, C): OK (0.84s)
        191  ns ± 3.1 ns, 424 B  allocated,  94 B  copied,  52 MB peak memory, 0.14x
    Packed bitwise AND, length 255
      packZipWith:                  OK (2.85s)
        2.69 μs ±  22 ns,  23 KB allocated,   7 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (6.91s)
        204  ns ± 1.7 ns, 359 B  allocated,  95 B  copied,  52 MB peak memory, 0.08x
      chunkedZipWith (2 blocks, C): OK (0.87s)
        199  ns ± 2.9 ns, 424 B  allocated,  94 B  copied,  52 MB peak memory, 0.07x
      chunkedZipWith (3 blocks):    OK (3.61s)
        213  ns ± 1.4 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.08x
      chunkedZipWith (3 blocks, C): OK (1.73s)
        201  ns ± 2.5 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.07x
    Packed bitwise AND, length 511
      packZipWith:                  OK (23.36s)
        5.60 μs ±  89 ns,  45 KB allocated,  11 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (1.92s)
        221  ns ± 4.2 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.04x
      chunkedZipWith (2 blocks, C): OK (14.52s)
        215  ns ± 3.8 ns, 431 B  allocated,  95 B  copied,  52 MB peak memory, 0.04x
      chunkedZipWith (3 blocks):    OK (2.05s)
        233  ns ± 4.3 ns, 353 B  allocated,  94 B  copied,  52 MB peak memory, 0.04x
      chunkedZipWith (3 blocks, C): OK (7.27s)
        214  ns ± 1.5 ns, 431 B  allocated,  95 B  copied,  52 MB peak memory, 0.04x
    Packed bitwise AND, length 1023
      packZipWith:                  OK (0.74s)
        11.2 μs ± 170 ns,  90 KB allocated,  30 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (4.85s)
        282  ns ± 1.8 ns, 358 B  allocated,  95 B  copied,  52 MB peak memory, 0.03x
      chunkedZipWith (2 blocks, C): OK (4.84s)
        280  ns ± 752 ps, 430 B  allocated,  95 B  copied,  52 MB peak memory, 0.02x
      chunkedZipWith (3 blocks):    OK (1.36s)
        305  ns ± 3.0 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.03x
      chunkedZipWith (3 blocks, C): OK (2.49s)
        283  ns ± 3.3 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.03x
    Packed bitwise AND, length 2047
      packZipWith:                  OK (2.95s)
        22.3 μs ± 350 ns, 181 KB allocated, 114 B  copied,  52 MB peak memory
      chunkedZipWith (2 blocks):    OK (1.79s)
        394  ns ± 2.7 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.02x
      chunkedZipWith (2 blocks, C): OK (3.43s)
        390  ns ± 6.4 ns, 427 B  allocated,  95 B  copied,  52 MB peak memory, 0.02x
      chunkedZipWith (3 blocks):    OK (1.87s)
        410  ns ± 5.8 ns, 347 B  allocated,  92 B  copied,  52 MB peak memory, 0.02x
      chunkedZipWith (3 blocks, C): OK (0.94s)
        392  ns ± 5.5 ns, 405 B  allocated,  90 B  copied,  52 MB peak memory, 0.02x
```

We observe that the third and fourth approaches beat out the second by a factor
of at least 2, with said factor increasing to ~50 towards the largest inputs.
However, there doesn't appear to be much difference between the third and fourth
approaches. Additionally, the C-implemented versions do not out-perform their
Haskell equivalents by a worthwhile margin, while marginally increasing
allocations.

### Bitwise complement

The results of our benchmarks given the methodology we described are below.
Throughout, `map` refers to the first approach, `chunkedMap (2 blocks)` refers
to the second approach, and `chunkMap (3 blocks)` refers to the third approach.
We also mark the C implementation of the second approach. All multipliers are
shown as multiples of the running time of the first approach on the same length
of data.

```
All
  Bitwise complement
    Bitwise complement, length 1
      map:                      OK (26.39s)
        24.0 ns ± 464 ps, 111 B  allocated,   0 B  copied,  45 MB peak memory
      chunkedMap (2 blocks):    OK (26.34s)
        199  ns ± 3.7 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 8.31x
      chunkedMap (2 blocks, C): OK (3.47s)
        205  ns ± 1.4 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 8.56x
      chunkMap (3 blocks):      OK (1.77s)
        206  ns ± 4.1 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 8.60x
    Bitwise complement, length 3
      map:                      OK (0.97s)
        28.0 ns ± 334 ps, 119 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (3.53s)
        209  ns ± 1.4 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 7.46x
      chunkedMap (2 blocks, C): OK (3.54s)
        210  ns ± 2.9 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 7.47x
      chunkMap (3 blocks):      OK (3.62s)
        214  ns ± 2.5 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 7.62x
    Bitwise complement, length 7
      map:                      OK (1.03s)
        29.8 ns ± 410 ps, 119 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (1.76s)
        207  ns ± 1.5 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 6.93x
      chunkedMap (2 blocks, C): OK (7.16s)
        213  ns ± 1.2 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 7.14x
      chunkMap (3 blocks):      OK (3.61s)
        214  ns ± 4.0 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 7.18x
    Bitwise complement, length 15
      map:                      OK (2.26s)
        33.4 ns ± 222 ps, 127 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (3.61s)
        214  ns ± 1.6 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 6.40x
      chunkedMap (2 blocks, C): OK (7.34s)
        219  ns ± 2.7 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 6.54x
      chunkMap (3 blocks):      OK (123.63s)
        234  ns ±  12 ns, 343 B  allocated,  96 B  copied,  53 MB peak memory, 7.01x
    Bitwise complement, length 31
      map:                      OK (1.36s)
        40.3 ns ± 548 ps, 143 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (122.95s)
        232  ns ± 806 ps, 343 B  allocated,  96 B  copied,  53 MB peak memory, 5.75x
      chunkedMap (2 blocks, C): OK (8.32s)
        247  ns ± 3.4 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 6.13x
      chunkMap (3 blocks):      OK (2.08s)
        245  ns ± 4.3 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 6.09x
    Bitwise complement, length 63
      map:                      OK (0.94s)
        54.2 ns ± 748 ps, 173 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (144.17s)
        276  ns ± 6.8 ns, 343 B  allocated,  96 B  copied,  53 MB peak memory, 5.10x
      chunkedMap (2 blocks, C): OK (1.17s)
        270  ns ± 4.2 ns, 330 B  allocated,  92 B  copied,  53 MB peak memory, 4.99x
      chunkMap (3 blocks):      OK (2.40s)
        281  ns ± 2.2 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 5.19x
    Bitwise complement, length 127
      map:                      OK (0.69s)
        78.7 ns ± 1.4 ns, 235 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (5.88s)
        174  ns ± 1.4 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 2.21x
      chunkedMap (2 blocks, C): OK (5.73s)
        169  ns ± 2.9 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 2.15x
      chunkMap (3 blocks):      OK (2.89s)
        169  ns ± 2.0 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 2.15x
    Bitwise complement, length 255
      map:                      OK (0.96s)
        111  ns ± 1.4 ns, 362 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (1.55s)
        176  ns ± 2.1 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 1.58x
      chunkedMap (2 blocks, C): OK (2.90s)
        166  ns ± 2.5 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 1.49x
      chunkMap (3 blocks):      OK (2.98s)
        173  ns ± 1.5 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 1.56x
    Bitwise complement, length 511
      map:                      OK (0.77s)
        175  ns ± 3.4 ns, 611 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (0.89s)
        195  ns ± 2.7 ns, 330 B  allocated,  92 B  copied,  53 MB peak memory, 1.11x
      chunkedMap (2 blocks, C): OK (12.96s)
        191  ns ± 186 ps, 343 B  allocated,  95 B  copied,  53 MB peak memory, 1.09x
      chunkMap (3 blocks):      OK (1.70s)
        192  ns ± 3.7 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 1.10x
    Bitwise complement, length 1023
      map:                      OK (1.34s)
        311  ns ± 2.8 ns, 1.1 KB allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (2.19s)
        246  ns ± 2.0 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 0.79x
      chunkedMap (2 blocks, C): OK (8.14s)
        236  ns ± 2.8 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 0.76x
      chunkMap (3 blocks):      OK (2.23s)
        248  ns ± 4.5 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 0.80x
    Bitwise complement, length 2047
      map:                      OK (0.66s)
        592  ns ±  11 ns, 2.1 KB allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (92.07s)
        342  ns ± 568 ps, 343 B  allocated,  96 B  copied,  53 MB peak memory, 0.58x
      chunkedMap (2 blocks, C): OK (21.84s)
        318  ns ± 780 ps, 343 B  allocated,  95 B  copied,  53 MB peak memory, 0.54x
      chunkMap (3 blocks):      OK (6.18s)
        354  ns ± 6.3 ns, 341 B  allocated,  95 B  copied,  53 MB peak memory, 0.60x
```

These results show that until the input length becomes significantly long
(around 1KiB), the first approach is much better (as much as a factor of 8). We
do see some improvement at the upper end of our sizes, but this amounts to about
a factor of 2 at most. The C implementation of the second approach does not seem
to give significant speedups; the third approach appears slower than the second
for all tested sizes.

To establish where the 'phase transition' between the first and second
approaches happens, we ran further benchmarks, limiting our sizes to the space
between 511 and 1023 bytes:

```
All
  Bitwise complement probe
    Bitwise complement probe, length 511
      map:                      OK (4.99s)
        147  ns ± 2.2 ns, 621 B  allocated,   0 B  copied,  45 MB peak memory
      chunkedMap (2 blocks):    OK (1.64s)
        182  ns ± 2.5 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 1.24x
      chunkedMap (2 blocks, C): OK (1.61s)
        181  ns ± 1.3 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 1.23x
      chunkMap (3 blocks):      OK (0.84s)
        183  ns ± 3.1 ns, 330 B  allocated,  92 B  copied,  53 MB peak memory, 1.25x
    Bitwise complement probe, length 767
      map:                      OK (0.88s)
        205  ns ± 2.7 ns, 875 B  allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (0.95s)
        206  ns ± 2.6 ns, 330 B  allocated,  92 B  copied,  53 MB peak memory, 1.00x
      chunkedMap (2 blocks, C): OK (6.91s)
        202  ns ± 1.1 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 0.99x
      chunkMap (3 blocks):      OK (1.85s)
        208  ns ± 3.1 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 1.02x
    Bitwise complement probe, length 1023
      map:                      OK (1.26s)
        295  ns ± 4.5 ns, 1.1 KB allocated,   0 B  copied,  53 MB peak memory
      chunkedMap (2 blocks):    OK (63.98s)
        238  ns ± 292 ps, 343 B  allocated,  95 B  copied,  53 MB peak memory, 0.81x
      chunkedMap (2 blocks, C): OK (7.89s)
        228  ns ± 3.2 ns, 343 B  allocated,  95 B  copied,  53 MB peak memory, 0.77x
      chunkMap (3 blocks):      OK (2.15s)
        242  ns ± 1.5 ns, 339 B  allocated,  94 B  copied,  53 MB peak memory, 0.82x
```

We note that at 767 bytes (exactly mid-way), the 'phase transition' has already
occurred.

### Population count

The results of our benchmark given the methodology we described are below.
Throughout, `foldl'` refers to the first approach, `chunkPopCount2 to the second
approach, and `chunkPopCount3` to the third approach. All multipliers are shown
as multiples of the running time of the first approach on the same length of
data.

```
All
  Popcount
    Popcount, length 1
      foldl':         OK (49.30s)
        22.9 ns ± 348 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (3.17s)
        23.3 ns ± 456 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.02x
      chunkPopCount3: OK (0.81s)
        24.1 ns ± 330 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.05x
    Popcount, length 3
      foldl':         OK (0.92s)
        27.1 ns ± 372 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (113.34s)
        26.7 ns ±  64 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.98x
      chunkPopCount3: OK (0.91s)
        26.8 ns ± 372 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.99x
    Popcount, length 7
      foldl':         OK (4.05s)
        30.3 ns ± 226 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (8.52s)
        31.9 ns ±  40 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.05x
      chunkPopCount3: OK (1.05s)
        31.2 ns ± 322 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.03x
    Popcount, length 15
      foldl':         OK (0.69s)
        40.4 ns ± 682 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (4.39s)
        32.8 ns ± 100 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.81x
      chunkPopCount3: OK (0.57s)
        33.6 ns ± 638 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.83x
    Popcount, length 31
      foldl':         OK (2.08s)
        61.9 ns ± 420 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (81.00s)
        37.8 ns ± 222 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.61x
      chunkPopCount3: OK (0.64s)
        37.6 ns ± 688 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.61x
    Popcount, length 63
      foldl':         OK (0.83s)
        99.5 ns ± 1.8 ns,  38 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (0.77s)
        45.2 ns ± 778 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.45x
      chunkPopCount3: OK (0.75s)
        44.7 ns ± 666 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.45x
    Popcount, length 127
      foldl':         OK (0.68s)
        161  ns ± 2.7 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (1.09s)
        64.0 ns ± 650 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.40x
      chunkPopCount3: OK (1.12s)
        66.7 ns ± 696 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.41x
    Popcount, length 255
      foldl':         OK (0.60s)
        287  ns ± 5.7 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (0.89s)
        104  ns ± 1.7 ns,  38 B  allocated,   0 B  copied,  47 MB peak memory, 0.36x
      chunkPopCount3: OK (0.86s)
        101  ns ± 1.6 ns,  38 B  allocated,   0 B  copied,  47 MB peak memory, 0.35x
    Popcount, length 511
      foldl':         OK (0.58s)
        538  ns ±  11 ns,   0 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (0.77s)
        181  ns ± 2.9 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory, 0.34x
      chunkPopCount3: OK (0.72s)
        167  ns ± 2.8 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory, 0.31x
    Popcount, length 1023
      foldl':         OK (1.11s)
        1.04 μs ±  11 ns,   0 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (0.73s)
        341  ns ± 5.3 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory, 0.33x
      chunkPopCount3: OK (1.28s)
        301  ns ± 2.7 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory, 0.29x
    Popcount, length 2047
      foldl':         OK (1.09s)
        2.05 μs ±  28 ns,   0 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount2: OK (0.69s)
        649  ns ±  12 ns,   0 B  allocated,   0 B  copied,  47 MB peak memory, 0.32x
      chunkPopCount3: OK (1.20s)
        568  ns ± 6.7 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory, 0.28x
```

We observe that, even for short inputs, the time required by the second and
third approach is not significantly worse than the first: the difference is at
most 5%, which at the scale being measured is barely distinct from noise. Once
the length reaches 15, there is about a 20% improvement in running time when
using the second and third approaches relative the first, and for lengths larger
than this, the increase only continues. Overall, the third approach does not
appear significantly better than the second until the input size reaches 511,
but isn't significantly worse at lengths above 15. To more clearly see the
difference, we also ran the same inputs, but compared the second approach to the
third:

```
All
  Block popcount
    Block popcount, length 1
      chunkPopCount2: OK (0.74s)
        20.5 ns ± 404 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (3.12s)
        23.3 ns ± 312 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.14x
    Block popcount, length 3
      chunkPopCount2: OK (3.31s)
        25.1 ns ± 134 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (1.70s)
        25.4 ns ± 352 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.01x
    Block popcount, length 7
      chunkPopCount2: OK (1.02s)
        30.2 ns ± 456 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (1.08s)
        32.2 ns ± 432 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.07x
    Block popcount, length 15
      chunkPopCount2: OK (1.09s)
        32.2 ns ± 366 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (1.06s)
        31.1 ns ± 400 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.97x
    Block popcount, length 31
      chunkPopCount2: OK (0.60s)
        35.2 ns ± 684 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (0.61s)
        36.3 ns ± 642 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 1.03x
    Block popcount, length 63
      chunkPopCount2: OK (0.76s)
        45.0 ns ± 772 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (2.96s)
        44.1 ns ± 174 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.98x
    Block popcount, length 127
      chunkPopCount2: OK (1.05s)
        62.0 ns ± 740 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (1.00s)
        59.3 ns ± 986 ps,  39 B  allocated,   0 B  copied,  47 MB peak memory, 0.96x
    Block popcount, length 255
      chunkPopCount2: OK (0.85s)
        100  ns ± 1.3 ns,  38 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (0.80s)
        93.4 ns ± 1.3 ns,  38 B  allocated,   0 B  copied,  47 MB peak memory, 0.93x
    Block popcount, length 511
      chunkPopCount2: OK (0.75s)
        175  ns ± 2.7 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (0.68s)
        160  ns ± 2.7 ns,  31 B  allocated,   0 B  copied,  47 MB peak memory, 0.91x
    Block popcount, length 1023
      chunkPopCount2: OK (0.70s)
        330  ns ± 5.2 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (0.63s)
        294  ns ± 5.5 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory, 0.89x
    Block popcount, length 2047
      chunkPopCount2: OK (1.32s)
        624  ns ± 5.6 ns,  25 B  allocated,   0 B  copied,  47 MB peak memory
      chunkPopCount3: OK (0.60s)
        562  ns ±  10 ns,   0 B  allocated,   0 B  copied,  47 MB peak memory, 0.90x
```

We can see that the benefits of the third approach versus the second amount to
10% better performance at most, and even that only occurs at length 511 and
higher. At the same time, for lengths below 15, there can be up to a 15% penalty
for using the third approach over the second.

## Conclusion and recommendations

We do not believe the use of the FFI and implementing any operations in
(portable C) to be worthwhile; there appear to be no significant gains in speed, 
and GHC appears able to generate code competitive with the C compiler.

For bitwise binary operations, we recommend a 'hybrid' approach: for smaller
input lengths (less than 30 items), we use the first (naive) approach, while for
anything larger, we use the third approach (with `Word64`-width
bit-parallelism). This would give us good performance on both small and large
inputs, and would not require a significant overhead, as we have to verify that
the lengths of our inputs match anyway.

For bitwise complement, we also recommend a 'hybrid' approach: for input lengths
less than 760 bytes, we use the first (naive) approach, while for anything
larger, we use the second approach (with `Word64`-width bit-parallelism). While
this would require some overhead for a length check, we believe that it's
worthwhile, as the length of an input `ByteString` is statically known. However,
if we consider inputs of this length unlikely relative the extra code path,
using the first approach in all cases is acceptable; however, we don't believe
that the extra code represents significant maintenance or runtime overheads, and
while inputs of this size would be unlikely, they're not impossible.

Popcount should be implemented using the second (`Word64`-width bit-parallel)
approach only. The first (naive) approach is not significantly better at any
length, and the third (`Word256`-width bit parallel) approach only out-performs
the second by a small margin for large inputs. While a 'hybrid' approach for
this operation may be possible in theory, the benefits relative the extra code
and its maintenance don't appear worthwhile.

## Future work

Many, if not most, of the operations here can be significantly accelerated using
[SIMD
instructions](https://en.wikipedia.org/wiki/Single_instruction,_multiple_data).
This is because many of the operations are bit-parallel or monoidal (bitwise
binary operations and population counting) while others can benefit from
instruction-level parallelism and wider words, as well as specialized
instructions. Given that this code will be run on Cardano nodes, which are
likely to be x86-64 machines with recent instruction sets, the gains are
potentially significant; at the same time, this would require significant extra
build-time checks, as well as fallbacks when said instructions are not
available.
