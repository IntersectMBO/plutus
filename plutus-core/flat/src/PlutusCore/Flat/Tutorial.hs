module PlutusCore.Flat.Tutorial
  ( -- $setup
    -- $main
  )
where

{-$setup
To (de)serialise a data type, make it an instance of the 'Flat.Class.Flat' class.

There is <https://hackage.haskell.org/package/base/docs/GHC-Generics.html Generics> based support to automatically derive a correct instance.

Let’s see some code.

We need a couple of extensions:

>>> :set -XDeriveGeneric -XDeriveAnyClass

The @Flat@ top module:

>>> import PlutusCore.Flat

And, just for fun, a couple of functions to display an encoded value as a sequence of bits:

>>> import PlutusCore.Flat.Instances.Test (flatBits,allBits)

Define a few custom data types, deriving @Generic@ and @Flat@:

>>> data Result = Bad | Good deriving (Show,Generic,Flat)

>>> data Direction = North | South | Center | East | West deriving (Show,Generic,Flat)

>>> data List a = Nil | Cons a (List a) deriving (Show,Generic,Flat) -}

{-$main
Now we can encode a List of Directions using 'Flat.Run.flat':

>>> flat $ Cons North (Cons South Nil)
"\149"

The result is a strict <https://hackage.haskell.org/package/bytestring/docs/Data-ByteString.html ByteString>.

And decode it back using 'Flat.Run.unflat':

>>> unflat . flat $ Cons North (Cons South Nil) :: Decoded (List Direction)
Right (Cons North (Cons South Nil))

The result is a 'Flat.Decoded' value: 'Either' a 'Flat.DecodeException' or the actual value.

=== Optimal Bit-Encoding
#optimal-bit-encoding#

A pecularity of Flat is that it uses an optimal bit-encoding rather than
the usual byte-oriented one.

One bit is sufficient to encode a 'Result' or an empty 'List':

>>> flatBits Good
"1"

>>> flatBits (Nil::List Direction)
"0"

Two or three bits suffice for a 'Direction':

>>> flatBits South
"01"

>>> flatBits West
"111"

For the serialisation to work with byte-oriented devices or storage, we need to add some padding.

To do so, rather than encoding a plain value, 'Flat.Run.flat' encodes a 'Flat.Filler.PostAligned' value, that's to say a value followed by a 'Flat.Filler.Filler' that stretches till the next byte boundary.

In practice, the padding is a, possibly empty, sequence of 0s followed by a 1.

For example, this list encodes as 7 bits:

>>> flatBits $ Cons North (Cons South Nil)
"1001010"

And, with the added padding of a final "1", will snugly fit in a single byte:

>>> allBits $ Cons North (Cons South Nil)
"10010101"

But .. you don't need to worry about these details as byte-padding is automatically added by the function 'Flat.Run.flat' and removed by 'Flat.Run.unflat'.

=== Pre-defined Instances

Flat instances are already defined for relevant types of some common packages: array, base, bytestring, containers, dlist, mono-traversable, text, unordered-containers, vector.

They are automatically imported by the "Flat" module.

For example:

>>> flatBits $ Just True
"11"

=== Wrapper Types

There are a few wrapper types that modify the way encoding and/or decoding occur.

* "Flat.AsBin" and "Flat.AsSize" decode to a value's flat binary representation or size in bits respectively.

* 'Flat.Instances.Mono.AsArray' and 'Flat.Instances.Mono.AsList' encode/decode a sequence as a List or Array respectively, see "Flat.Instances.Mono" for details.

* 'Flat.Instances.Text.UTF8Text' and 'Flat.Instances.Text.UTF16Text' encode/decode a Text as UTF8 or UTF16 respectively. -}
