## Type erasure and CBOR sizes for Plutus Core

This document describes some experiments looking at how erasing
various things from the Plutus Core AST affects the size of serialised
programs.  The full Plutus Core AST contains type information and
human-readable names, neither of which are necessary for evaluation,
so we may not need to keep them around.  This is related to issues
[#1592](https://github.com/input-output-hk/plutus/issues/1592) and
[#1524](https://github.com/input-output-hk/plutus/issues/1524) on
GitHub.  The next step will be to look at Merklisation.

I've implemented two basic transformations:

#### Type erasure

This converts the Plutus Core AST into an untyped version.  The
untyped version discards the constructors for type abstraction,
type-level application, and the `iwrap` and `unwrap` operations,
leaving only six kinds of AST node: variables, lambda abstraction,
application, the `error` term, constants, and application of built-in
functions.  There are versions of the CK and CEK machines which
interpret this, giving identical results to the typed versions.

#### Removing names
The names of variables and types in the AST are represented by the type

```
data Name ann = Name
    { nameAttribute :: ann
    , nameString    :: T.Text -- ^ The identifier name, for use in error messages.
    , nameUnique    :: Unique -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
    }
```

The `name` type (and also the type of AST nodes) is parametric over a
type `ann` of annotations.  This is the unit type by the time we get
executable PLC.  Names also contain human-readable identifiers, but
these are irrelevant for evaluation.  The only thing that is really
important is the `Unique` identifier in the name, which is essentially
an `Int`.  I've implemented two name-erasure functions: one which
replaces all of the strings with the empty string, and one which
discards annotations and identifier strings, essentially leaving just
an integer.  Annotations are discarded in names, but not in general
AST nodes, because they'll be useful for Merklisation.

###### De Bruijn indices
There's some existing code for converting names into de Bruijn indices
to make comparison of terms easier (there's no evaluator for this at the moment).
I also wrote a function which replaces names by an integer representing their
de Bruijn indices.  This turns out to be surprisingly effective.

### Results

Plutus Core ASTs are serialised into bytestrings using the
[CBOR](http://hackage.haskell.org/package/serialise) format.  I
applied various transformations to the ASTs for the validator code for
the Plutus [use
cases](https://github.com/input-output-hk/plutus/tree/master/plutus-use-cases)
in the Plutus repository, serialised to CBOR, and measured the number
of bytes in the output (I had to cheat slightly to replace some dynamic
builtin names with standard ones, but I don't think that'll affect the
results; I'm in the process of fixing that at the moment).  I also
compressed the results using `gzip -9` and measured the size again.
The results are shown in the table below.  The figures in brackets
after some entries show their size as a percentage of the size of the
serialised version of the full AST.

Deleting unnecessary information and compressing reduces the size of
the CBOR to less than 10K in every case, with the size decreasing by a
factor of 20 or more (except for the swap contract, at 5.4%) (compare
the top left and second from right on the bottom for each contract).  Even
without compression, type erasure and name anonymisation reduces sizes
by a factor of 6 or more.

If we delete types and replacing names with de Bruijn indices then
the size the CBOR is consistently reduced by a factor of about ten
compared with the typed CBOR.  With compression, the size is reduced
by a factor of 40 to 100.  I thinnk there are two reasons for this

 1. De Bruijn indices are generally small: in the examples I looked
    at, the largest index was typically about 200, compared with
    several thousand for the version involving unique integer
    identifiers for names.  This means that they fit into a single byte and
    CBOR can encode them more efficiently.

 2. Using de Bruijn indices will make more terms equal to each other, and
    this will make the CBOR more amenable to compression


Clearly, removing types and name strings helps a lot with sizes.  The
CBOR representation is very small (six tags for AST nodes types and
about twenty for built-in names, plus standard CBOR encodings for
constants and names of extensible built-ins), which probably accounts
for its compressability.  The uncompressed CBOR is sufficiently simple
that we might well be able to execute it directly without having to
decode most of it back to Haskell types.  It's beginning to look a lot
like bytecode ...


| Contract | Compression | Typed | Typed, empty names | Untyped | Untyped, empty names | Untyped, no names | Untyped, deBruijn |
| --- | --- | ---: | ---: |---: | ---: | ---: | ---: |
| CrowdFunding | Uncompressed | 111142 | 80159 | 29056 | 18990 | 14356 (12.9%)| 10295 (9.3%)| 
|              | Compressed   | 20953  | 17376 | 7283  | 5208  | 5079 (4.6%) | 1637 (1.5%)|
| | | | || | | |
| | | | || | | |
| Currency | Uncompressed | 154418 | 108541 |45217 | 27716 | 21020 (13.6%) | 15536 (10.1%) |
|              | Compressed   | 27549  | 22871 | 10028 | 7391 | 7210 (4.7%)| 2994 (1.9%) |
| | | | || | | |
| | | | || | | |
| Escrow | Uncompressed | 126659 | 91052 |34880 | 22653 | 17181 (13.6%) | 12788 (10.1%)
|              | Compressed   | 23292  | 19506 | 8196 | 5973 | 5820 (4.6%)| 2098 (1.7%)
| | | | || | | |
| | | | || | | |
| Future | Uncompressed | 174512 | 120857 |53726 | 32461 | 24483 (14.0%) | 17418 (10.0%) |
|              | Compressed   | 31083  | 25593 | 11945 | 8772 | 8551 (4.9%)| 3565 (2.0%) |
| | | | || | | |
| | | | || | | |
| Game | Uncompressed | 93097 | 60178 |29973 | 16700 | 12466 (13.4%)| 9268 (10.0%) | 9268 (10.0%) |
|              | Compressed   | 15653  | 12487 | 6156 | 4301 | 4181 (4.5%)| (1.2%) | 2118 (2.3%) |
| | | | || | | |
| | | | || | | |
| GameStateMachine | Uncompressed | 111711 | 81440 |31298 | 21477 | 16899 (15.1%) | 13538 (12.1%)|
|              | Compressed   | 20658  | 17042 | 6979 | 4938 | 4827 (4.3%) | 2058 (1.8%) |
| | | | || | | |
| | | | || | | |
| MultiSig | Uncompressed | 105672 | 69951 |34650 | 20058 | 15110 (14.3%)| 11228 (10.6%) |
|              | Compressed   | 18388  | 14775 | 7416 | 5220 | 5083 (4.8%)| 2446 (2.3%) |
| | | | || | | |
| | | | || | | |
| MultiSigStateMachine | Uncompressed | 198807 | 145619 |59359 | 39226 | 30504 (15.3%)| 22878 (11.5%) |
|              | Compressed   | 36372  | 30477 | 13063 | 9620 | 9413 (4.7%)| (2.0%) |
| | | | || | | |
| | | | || | | |
| PubKey | Uncompressed | 100811 | 66142 |33117 | 18960 | 14254 (14.1%)| 10693 (10.6%) |
|              | Compressed   | 17193  | 13775 | 6913 | 4887 | 4758 (4.7%)| 2356 (2.3%) |
| | | | || | | |
| | | | || | | |
| Swap | Uncompressed | 152252 | 101923 |54848 | 32442 | 24604 (16.2%)| 17739 (11.7%) |
|              | Compressed   | 26725  | 21548 | 11782 | 8495 | 8268 (5.4%) | 3770 (2.5%) |
| | | | || | | |
| | | | || | | |
| TokenAccount | Uncompressed | 78001 | 57508 |14164 | 9603 | 7189 (9.2%)| 4994 (6.4%) |
|              | Compressed   | 15469  | 13026 | 4324 | 2905 | 2833 (3.6%) | 747 (1.0%) |
| | | | || | | |
| | | | || | | |
| Vesting      | Uncompressed | 192764 | 135261 |57402 | 35105 | 26489 (13.7%) | 18878 (9.8%) |
|              | Compressed   | 33517  | 27937 | 12413 | 9335 |  9100 (4.7%) | 3598 (1.9%) |