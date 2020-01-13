## 1. Type erasure and CBOR sizes for Plutus Core 

This document describes some experiments looking at how erasing
various things from the Plutus Core AST affects the size of serialised
programs.  The full Plutus Core AST contains type information and
human-readable names, neither of which are necessary for evaluation,
so we may not need to keep them around.  This is related to issues
[#1592](https://github.com/input-output-hk/plutus/issues/1592) and
[#1524](https://github.com/input-output-hk/plutus/issues/1524) on
GitHub.  Merklisation is considered in
[Merklisation-notes.md](./Merklisation-notes.md) and
[Merklising-programs.md](./Merklising-programs.md).

See [PLC-AST-types.md](./PLC-AST-types.md) for a summary of the structure of Plutus Core ASTs.

See also [AST-analysis.md](./AST-analysis.md) for some basic
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
discards the identifier strings, and one which
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

The experiments here were all carried out on (unapplied) validator
scripts from the the Plutus [use
cases](https://github.com/input-output-hk/plutus/tree/master/plutus-use-cases)
in the Plutus repository.  Plutus Core ASTs were obtained from Haskell
source using the PlutusTx compiler infrastructure and then serialised
into bytestrings using the
[CBOR](http://hackage.haskell.org/package/serialise) format.  I
applied various transformations to the ASTs before serialising and
then measured the number of bytes in the output.  I also compressed
the results (using `gzip` with maximum compression) and measured the
size again.  The results are shown in the table below.  The figures in
brackets after some entries show their size as a percentage of the
size of the serialised version of the full AST.  All of the ASTs here
are annotated with units, which take up space when serialised.  The
final column of the table shows what happens when these unit
annotations are not included in the serialised form (it's safe to do
this because we know where they will occur so can insert them
automatically when deserialising, although maybe on-chain ASTs
shouldn't have annotations at all).  

The are a large number of possible combinations of the transformations
mentioned above and the table only contains a limited number of these
in order to save space.  It would be quite easy to get figures for
other combinations as well if necessary.

The table below may be too wide for the page, but if you click on it you
can use left and right arrow keys to scroll horizontally.

| Contract | Compression | Typed | Typed, stringless names | Untyped | Untyped, stringless names | Untyped, integer IDs only | Untyped, de Bruijn | Untyped, de Bruijn, annotations not serialised
| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Crowdfunding |  Uncompressed | 110413 | 70174 | 28796 | 16330 | 13995 (12.7%) | 10384 (9.4%) | 6593 (6.0%) | 
|     | Compressed | 21440 | 17761 | 7449 | 5318 | 5222 (4.7%) | 1703 (1.5%) | 1541 (1.4%) | 
| |
| |
| Currrency |  Uncompressed | 159160 | 97971 | 47453 | 25045 | 21467 (13.5%) | 16581 (10.4%) | 10655 (6.7%) | 
|     | Compressed | 29004 | 23878 | 10762 | 7908 | 7796 (4.9%) | 3248 (2.0%) | 3010 (1.9%) | 
| |
| |
| Escrow |  Uncompressed | 117438 | 74407 | 31739 | 17963 | 15460 (13.2%) | 11992 (10.2%) | 7653 (6.5%) | 
|     | Compressed | 22064 | 18269 | 7603 | 5483 | 5373 (4.6%) | 2053 (1.7%) | 1882 (1.6%) | 
| |
| |
| Future |  Uncompressed | 206137 | 133307 | 55018 | 31504 | 27354 (13.3%) | 21810 (10.6%) | 13914 (6.7%) | 
|     | Compressed | 40134 | 33562 | 12900 | 9356 | 9203 (4.5%) | 3688 (1.8%) | 3394 (1.6%) | 
| |
| |
| Game |  Uncompressed | 98970 | 55737 | 32334 | 15382 | 13043 (13.2%) | 10265 (10.4%) |  6635 (6.7%) | 
|     | Compressed | 16898 | 13436 | 6781 | 4804 | 4708 (4.8%) | 2329 (2.4%) | 2148 (2.2%) | 
| |
| |
| GameStateMachine |  Uncompressed | 117053 | 75933 | 31984 | 19277 | 16852 (14.4%) | 14116 (12.1%) |  8997 (7.7%) | 
|     | Compressed | 22322 | 18329 | 7455 | 5328 | 5243 (4.5%) | 2164 (1.8%) | 1980 (1.7%) | 
| |
| |
| MultiSig |  Uncompressed | 111990 | 64656 | 37528 | 18679 | 15943 (14.2%) | 12627 (11.3%) | 8149 (7.3%) | 
|     | Compressed | 19771 | 15850 | 8100 | 5792 | 5686 (5.1%) | 2772 (2.5%) | 2552 (2.3%) | 
| |
| |
| MultiSigStateMachine |  Uncompressed | 196628 | 126342 | 58798 | 33794 | 29307 (14.9%) | 23420 (11.9%) |  14956 (7.6%) | 
|     | Compressed | 37535 | 31232 | 13577 | 9945 | 9801 (5.0%) | 4045 (2.1%) | 3719 (1.9%) | 
| |
| |
| PubKey |  Uncompressed | 106535 | 60877 | 35498 | 17396 | 14816 (13.9%) | 11730 (11.0%) | 7579 (7.1%) | 
|     | Compressed | 18483 | 14776 | 7563 | 5412 | 5326 (5.0%) | 2612 (2.5%) | 2409 (2.3%) | 
| |
| |
| Swap |  Uncompressed | 154724 | 89748 | 56395 | 28580 | 24432 (15.8%) | 18785 (12.1%) | 12077 (7.8%) | 
|     | Compressed | 28243 | 22596 | 12597 | 9069 | 8915 (5.8%) | 4056 (2.6%) |  3756 (2.4%) | 
| |
| |
| TokenAccount |  Uncompressed | 78030 | 50888 | 14172 | 8305 | 7082 (9.1%) | 5053 (6.5%) | 3184 (4.1%) | 
|     | Compressed | 15765 | 13205 | 4402 | 2969 | 2929 (3.8%) | 743 (1.0%) |  659 (0.8%) | 
| |
| |
| Vesting |  Uncompressed | 119514 | 76615 | 30089 | 17252 | 14784 (12.4%) | 10976 (9.2%) |  6967 (5.8%) | 
|     | Compressed | 23348 | 19473 | 7866 | 5671 | 5582 (4.7%) | 1783 (1.5%) |  1614 (1.4%) | 

Note also that the only column where unit annotations are not
serialised is the final one; we can get substantial savings on the
other columns by doing the same there, but this is not shown in the
table.

See [FixpointSharing.md](./FixpointSharing.md) for a version of this
table where the compiler optimises the code by sharing the (sizeable)
fixpoint combinator instead of generating multiple instances.


### Conclusions

Deleting unnecessary information and compressing reduces the size of
the CBOR to less than 10K in every case, with the size decreasing by a
factor of 20 or more (except for the swap contract, at 5.6%) (compare
the top left and third from right on the bottom for each contract).  Even
without compression, type erasure and name anonymisation reduces sizes
by a factor of 6 or more.

If we delete types and replace names with de Bruijn indices then the
size the CBOR is consistently reduced by a factor of about 10
compared to the typed CBOR.  With compression, the size is reduced
by a factor of 40 to 100, and is never more than half the size of the
version involving names which are just integer IDs (the previous
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

I'm not sure how easy it would be to evaluate code which uses de
Bruijn indices, but this is arguably irrelevant: one could use the de
Bruijn version of a program as a transporation format and convert back
to the original identifier scheme on the chain (although this would
obviously incur an extra cost, as would compression and
decompression).  Another problem with these transformations is that
they will change the hash of scripts, and hashes are generally
used as unique addresses for scripts.

**Update**: see [Compressibility.md](./Compressibility.md) for an
  investigation of why serialised ASTs are so compressible.

Clearly, removing types and name strings helps a lot with sizes.  The
CBOR representation is very small (six tags for AST nodes types and
about twenty for built-in names, plus standard CBOR encodings for
constants and names of extensible built-ins), which probably accounts
for its compressibility.  The uncompressed CBOR is sufficiently simple
that we might well be able to execute it directly without having to
decode most of it back to Haskell types.  This is beginning to look
rather like bytecode...

