## Extending bytestring operations in PlutusTx and Plutus Core
(19th November 2020)

In a [Slack thread](https://input-output-rnd.slack.com/archives/C21UF2WVC/p1599120765047200)
some time ago, Alex asked about extending support for bytestrings in Plutus Core.
This document describes the issue and suggests some possible extensions.


### Current bytestring support in PLC

Plutus Core currently provides the following operations for its built-in
bytestring type:

   * `concatenate`
   * `equalsByteString`
   * `lessThanByteString`
   * `greaterThanByteString`
   * `takeByteString`
   * `dropByteString`
   * `sha2_256`
   * `sha3_256`
   * `verifySignature`

The `concatenate` function might be better called `appendByteString`.  The PLC
specification also mentions an `emptyByteString` builtin, but we don't support
that.  However we do provide concrete syntax for bytestrings:
`(con bytestring #91ef22)` for example; `(con bytestring #)` represents the empty bytestring.

The problem is that there is no easy way to _construct_ a bytestring in Haskell
and convert it into a PLC bytestring, or to programatically construct a new
bytestring inside a Plutus Core program.  The `Data` type supports bytestrings
and can be used to pass bytestrings into validators, but this isn't very
general-purpose.


### Characters and strings in Plutus Core

Plutus Core also provides built-in character and string types.  These both have
concrete syntactical representations: `(con char 'q')` and `(con string
"something")`.  Support for these is very limited: we only have `charToString`
and `append` (append one string to another); also the PlutusTx compiler can
compile literal Haskell strings and characters into PLC values of the
appropriate types (but see below for some complications involving Strings).

However there is a subtlety: Plutus Core actually has _two_ representations of
Haskell Strings.  The PlutusTx plugin compiles normal Haskell strings into
Scott-encoded lists of PLC's `char` type ("Scott strings" for short), but there
is also a special type called `Language.PlutusTx.Builtins.String` which is
compiled into PLCs' `string` type.  Many standard string operations can be
compiled into PLC code acting on Scott strings, but support for builtin strings
in PlutusTx is limited.

**Update:** in the PR comments it's been suggested that we should
  switch to [`Data.Text`](https://hackage.haskell.org/package/text-1.2.4.1/docs/Data-Text.html) as the underlying type for character strings
  and do away with Scott strings altogether.  This might be sensible, but it could need quite a lot of work in the Plutus compiler.

### Bytestrings in Haskell

Plutus Core bytestrings are implemented using Haskell's (strict) `ByteString`
type from `Data.ByteString`.  Internally these are implemented as arrays of
`Word8` values.  Haskell doesn't provide any concrete syntax for the
`ByteString` type, but there are functions `pack :: [Word8] -> ByteString` and
`unpack :: ByteString -> [Word8]` which convert back and forth between
`ByteString`s and lists of `Word8` values.

One way (and possbily the most efficient way) to improve support for bytestrings
in Plutus Core would be to add the `Word8` type to the default PLC universe, but
this would add quite a lot of complexity that we probably don't want.  [However,
SCP-1091 proposes bit operations for Plutus Core, and we might want some kind of
`Word` type for that.]

Fortunately Haskell also provides the `Data.ByteString.Char8` interface to its
`ByteString` type; this provides, for instance, functions `pack :: String ->
ByteString` and `unpack :: ByteString -> String` which convert between `String`
and `ByteString`.  We already have support for strings and bytestrings in Plutus
Core, so this looks like a more promising way to provide extended bytestring
functionality.

The `pack` function operates on the ASCII codes of the characters in a string, so
`pack "91ef22"` would give you the bytestring `#393165663232`, not `#91ef22`;
however you could get the latter via `pack "\x91\xef\x22"` for example.  Also,
Strings are lists of Unicode characters and `pack` truncates these to the lowest
8 bits.

The `Char8` interface also provides an `IsString` instance for `ByteString`, and
this effectively gives you simple concrete syntax: using `OverloadedStrings`,
`"\x91\xef\x22"` can be automatically converted into a Bytestring.

### What should we add to PLC?

The simplest way to improve bytestring support in PLC would probably be to add a
`stringToBytestring` builtin implemented in terms of `Data.ByteString.Char8`.
For efficiency reasons we should probably use built-in PLC strings rather than
Scott strings.

As noted above, support for built-in strings is limited, so we may also need to
add some extra builtins for these at both the PlutusTx and PLC levels.

Here's an initial proposal for some new Plutus Core builtins to improve bytestring support.

  * `stringToBytestring`, converting built-in PLC strings to bytestrings and implemented using `pack`.
     I think that in conjuction with `OverloadedStrings` this would make it reasonably easy to convert
     "literal" Haskell ByteStrings to PLC bytestrings.
  * `integerToChar`, implemented using `Data.Char.chr`.  This could be used to build bytestrings at execution time.
    `consChar` (see below) would help with this.
  * A `consChar` operation allowing you to prepend a character to a PLC string. This would help with
    building bytestrings dynamically.  Also, `PlutusTx.String` contains
    a `stringToBuiltinString` function which converts Haskell `String` to `Builtin.String` by
    repeated application of `charToString` and `appendString`, which is not very efficient.  I think that
   `consChar` would allow us to implement this a low more efficiently.
  * Alternatively, a `consByte` operation directly adding a character or integer to the front of a bytestring.
    `Data.Bytestring.Char8.cons` would be helpful for this.
  * Perhaps also
     * A `lengthOfBytestring` function
     * An `indexBytestring` function allowing you to retrieve the character or integer at a given position in a bytestring.
     * `charToInteger`, the inverse of `integerToChar` (implemented as `Data.Char.ord`).

Any new PLC builtins should be mirrored in PlutusTx, but this should be
reasonably straightforward since everything mentioned above is based on existing
Haskell functions.
