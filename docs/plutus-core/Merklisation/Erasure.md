## Type erasure and CBOR sizes for Plutus Core

[kwxm, November 2019]

This document describes some experiments looking at how erasing
various things from the Plutus Core AST affects the size of serialised
programs.  The full Plutus Core AST contains type information and
human-readable names, neither of which are necessary for evaluation,
so we may not need to keep them around.  This is related to issues
[#1592](https://github.com/input-output-hk/plutus/issues/1592) and
[#1524](https://github.com/input-output-hk/plutus/issues/1524) on
GitHub.  The next step will be to look at Merklisation.

See also [ast-analysis.md](./ast-analysis.md) for some basic
statistics about the number and types of nodes in Plutus Core ASTs.

I've implemented two basic transformations:

#### Type erasure

This converts the Plutus Core AST into an untyped version.  The
untyped version discards the constructors for type abstraction,
type-level application, and the `iwrap` and `unwrap` operations,
leaving only six kinds of AST node: variables, lambda abstraction,
application, the `error` term, built-in constants, and names of
built-in functions.  (Note that the implementation diverges from the
specification here. The specification says that we have a special term
for application of built-in functions, and that these must always be
fully applied; however the implementation just has a term for names of
built-in functions, and these and lambda terms are applied using the
same constructor, `Apply`.)

There are versions of the CK and CEK machines which interpret untyped
ASTs, and they give identical results to the machines for the typed
version (modulo erasure of types).

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
an integer.  Annotations are discarded in names but not in general AST
nodes because they'll be useful for Merklisation there (but if we
decide not to go for Merklisation we should probably get rid of annotations
altogether in on-chain code since this will reduce sizes even further).

##### De Bruijn indices
There's some existing code for converting names into de Bruijn indices
to make comparison of terms easier (there's no evaluator for this at the moment).
I also wrote a function which replaces names by an integer representing their
de Bruijn indices.  This turns out to be surprisingly effective.

### Results

The experiments here were all carried out on validator scripts from
the the Plutus [use cases](https://github.com/input-output-hk/plutus/tree/master/plutus-use-cases)
in the Plutus repository.  Plutus Core ASTs were obtained from Haskell
source using the PlutusTx compiler infrastructure and then serialised
into bytestrings using the
[CBOR](http://hackage.haskell.org/package/serialise) format.  I
applied various transformations to the ASTs before serialising and
then measured the number of bytes in the output.  I also compressed the
results (using `gzip` with maximum compression) and measured the size
again.  The results are shown in the table below.  The figures in
brackets after some entries show their size as a percentage of the
size of the serialised version of the full AST.

Deleting unnecessary information and compressing reduces the size of
the CBOR to less than 10K in every case, with the size decreasing by a
factor of 20 or more (except for the swap contract, at 5.4%) (compare
the top left and second from right on the bottom for each contract).  Even
without compression, type erasure and name anonymisation reduces sizes
by a factor of 6 or more.

If we delete types and replace names with de Bruijn indices then the
size the CBOR is consistently reduced by a factor of about 10
compared to the typed CBOR.  With compression, the size is reduced
by a factor of 40 to 100, and is never more than half the size of the
version involving name which are just integer IDs (the previous
column).  I think there are two reasons for this

 1. De Bruijn indices are generally small: in the examples I looked
    at, the largest index was typically about 200, compared with
    several thousand for the version involving unique integer
    identifiers for names.  This means that they fit into a single
    byte and CBOR can encode them more efficiently.

 2. Using de Bruijn indices will make more terms equal to each other, and
    this will make the CBOR more amenable to compression

The fact that the de Bruijn version is significantly more compressible
than the non-de Bruijn version suggests that there will be significant
opportunities for optimisation in the original Plutus Core code.  Some
caution is required however: optimisations may be more effective in
the type-erased code (probably more things are equal than in the typed
version), but performing post-erasure optimisations would break the
clean correspondence between typed off-chain code and untyped on-chain
code.

### Conclusion

Clearly, removing types and name strings helps a lot with sizes.  The
CBOR representation is very small (six tags for AST nodes types and
about twenty for built-in names, plus standard CBOR encodings for
constants and names of extensible built-ins), which probably accounts
for its compressibility.  The uncompressed CBOR is sufficiently simple
that we might well be able to execute it directly without having to
decode most of it back to Haskell types.  It's beginning to look a lot
like bytecode ...


| Contract | Compression | Typed | Typed, empty names | Untyped | Untyped, empty names | Untyped, no names | Untyped, de Bruijn |
| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Crowdfunding |  Uncompressed| 108939 | 77981 | 28568 | 18527 | 13893 (12.8%) | 10317 (9.5%) | 
|     | Compressed | 21203 | 17701 | 7397 | 5348 | 5211 (4.8%) | 1697 (1.6%) | 
| |
| |
| Currrency |  Uncompressed| 150733 | 104849 | 44331 | 26877 | 20173 (13.4%) | 15583 (10.3%) | 
|     | Compressed | 27746 | 23044 | 10195 | 7531 | 7322 (4.9%) | 3042 (2.0%) | 
| |
| |
| Escrow |  Uncompressed| 123775 | 88197 | 34168 | 21970 | 16498 (13.3%) | 12813 (10.4%) | 
|     | Compressed | 23490 | 19696 | 8294 | 6110 | 5929 (4.8%) | 2144 (1.7%) | 
| |
| |
| Future |  Uncompressed| 167320 | 113732 | 52203 | 31005 | 23027 (13.8%) | 17438 (10.4%) | 
|     | Compressed | 31178 | 25735 | 12201 | 8966 | 8699 (5.2%) | 3591 (2.1%) | 
| |
| |
| Game |  Uncompressed| 90960 | 58067 | 29252 | 16005 | 11771 (12.9%) | 9275 (10.2%) | 
|     | Compressed | 15743 | 12649 | 6216 | 4399 | 4264 (4.7%) | 2130 (2.3%) | 
| |
| |
| GameStateMachine |  Uncompressed| 109276 | 79022 | 30444 | 20640 | 16062 (14.7%) | 13561 (12.4%) | 
|     | Compressed | 20773 | 17241 | 7015 | 5065 | 4937 (4.5%) | 2100 (1.9%) | 
| |
| |
| MultiSig |  Uncompressed| 103038 | 67350 | 33776 | 19217 | 14269 (13.8%) | 11257 (10.9%) | 
|     | Compressed | 18502 | 14957 | 7455 | 5361 | 5204 (5.1%) | 2486 (2.4%) | 
| |
| |
| MultiSigStateMachine |  Uncompressed| 190516 | 137385 | 57364 | 37288 | 28566 (15.0%) | 22904 (12.0%) | 
|     | Compressed | 36465 | 30686 | 13151 | 9738 | 9505 (5.0%) | 3979 (2.1%) | 
| |
| |
| PubKey |  Uncompressed| 98492 | 63788 | 32408 | 18254 | 13540 (13.7%) | 10740 (10.9%) | 
|     | Compressed | 17331 | 13987 | 6979 | 5014 | 4866 (4.9%) | 2401 (2.4%) | 
| |
| |
| Swap |  Uncompressed| 146143 | 95861 | 53271 | 30976 | 23130 (15.8%) | 17787 (12.2%) | 
|     | Compressed | 27001 | 21852 | 11984 | 8726 | 8471 (5.8%) | 3869 (2.6%) | 
| |
| |
| TokenAccount |  Uncompressed| 76763 | 56277 | 13958 | 9404 | 6990 (9.1%) | 4993 (6.5%) | 
|     | Compressed | 15454 | 13107 | 4343 | 2946 | 2869 (3.7%) | 746 (1.0%) | 
| |
| |
| Vesting |  Uncompressed| 186134 | 128686 | 55738 | 33496 | 24880 (13.4%) | 18887 (10.1%) | 
|     | Compressed | 33804 | 28236 | 12716 | 9536 | 9270 (5.0%) | 3660 (2.0%) | 
