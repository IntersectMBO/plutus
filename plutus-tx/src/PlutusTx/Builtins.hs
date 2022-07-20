-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

-- | Primitive names and functions for working with Plutus Core builtins.
module PlutusTx.Builtins (
                                -- * Bytestring builtins
                                BuiltinByteString
                                , appendByteString
                                , consByteString
                                , sliceByteString
                                , lengthOfByteString
                                , indexByteString
                                , emptyByteString
                                , equalsByteString
                                , lessThanByteString
                                , lessThanEqualsByteString
                                , greaterThanByteString
                                , greaterThanEqualsByteString
                                , sha2_256
                                , sha3_256
                                , blake2b_256
                                , verifyEd25519Signature
                                , verifyEcdsaSecp256k1Signature
                                , verifySchnorrSecp256k1Signature
                                , decodeUtf8
                                -- * Integer builtins
                                , Integer
                                , addInteger
                                , subtractInteger
                                , multiplyInteger
                                , divideInteger
                                , modInteger
                                , quotientInteger
                                , remainderInteger
                                , greaterThanInteger
                                , greaterThanEqualsInteger
                                , lessThanInteger
                                , lessThanEqualsInteger
                                , equalsInteger
                                -- * Error
                                , error
                                -- * Data
                                , BuiltinData
                                , chooseData
                                , matchData
                                , matchData'
                                , equalsData
                                , serialiseData
                                , mkConstr
                                , mkMap
                                , mkList
                                , mkI
                                , mkB
                                , unsafeDataAsConstr
                                , unsafeDataAsMap
                                , unsafeDataAsList
                                , unsafeDataAsI
                                , unsafeDataAsB
                                , BI.builtinDataToData
                                , BI.dataToBuiltinData
                                -- * Strings
                                , BuiltinString
                                , appendString
                                , emptyString
                                , equalsString
                                , encodeUtf8
                                -- * Lists
                                , matchList
                                -- * Tracing
                                , showInteger
                                , showBool
                                , showString
                                , showByteString
                                , showData
                                , trace
                                -- * Conversions
                                , fromBuiltin
                                , toBuiltin
                                -- * Bitwise builtins
                                , integerToByteString
                                , byteStringToInteger
                                , andByteString
                                , iorByteString
                                , xorByteString
                                , complementByteString
                                , shiftByteString
                                , rotateByteString
                                , popCountByteString
                                , testBitByteString
                                , writeBitByteString
                                , findFirstSetByteString
                                ) where

import PlutusTx.Base (const, uncurry)
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Class
import PlutusTx.Builtins.Internal (BuiltinByteString (..), BuiltinData, BuiltinString)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Integer (Integer)

{-# INLINABLE appendByteString #-}
-- | Concatenates two 'ByteString's.
appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString = BI.appendByteString

{-# INLINABLE consByteString #-}
-- | Adds a byte to the front of a 'ByteString'.
consByteString :: Integer -> BuiltinByteString -> BuiltinByteString
consByteString n bs = BI.consByteString (toBuiltin n) bs

{-# INLINABLE sliceByteString #-}
-- | Returns the substring of a 'ByteString' from index 'start' of length 'n'.
sliceByteString :: Integer -> Integer -> BuiltinByteString -> BuiltinByteString
sliceByteString start n bs = BI.sliceByteString (toBuiltin start) (toBuiltin n) bs

{-# INLINABLE lengthOfByteString #-}
-- | Returns the length of a 'ByteString'.
lengthOfByteString :: BuiltinByteString -> Integer
lengthOfByteString = BI.lengthOfByteString

{-# INLINABLE indexByteString #-}
-- | Returns the byte of a 'ByteString' at index.
indexByteString :: BuiltinByteString -> Integer -> Integer
indexByteString b n = BI.indexByteString b (toBuiltin n)

{-# INLINABLE emptyByteString #-}
-- | An empty 'ByteString'.
emptyByteString :: BuiltinByteString
emptyByteString = BI.emptyByteString

{-# INLINABLE sha2_256 #-}
-- | The SHA2-256 hash of a 'ByteString'
sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 = BI.sha2_256

{-# INLINABLE sha3_256 #-}
-- | The SHA3-256 hash of a 'ByteString'
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 = BI.sha3_256

{-# INLINABLE blake2b_256 #-}
-- | The BLAKE2B-256 hash of a 'ByteString'
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 = BI.blake2b_256

{-# INLINABLE verifyEd25519Signature #-}
-- | Ed25519 signature verification. Verify that the signature is a signature of
-- the message by the public key. This will fail if key or the signature are not
-- of the expected length.
verifyEd25519Signature
    :: BuiltinByteString  -- ^ Public Key (32 bytes)
    -> BuiltinByteString  -- ^ Message    (arbirtary length)
    -> BuiltinByteString  -- ^ Signature  (64 bytes)
    -> Bool
verifyEd25519Signature pubKey message signature = fromBuiltin (BI.verifyEd25519Signature pubKey message signature)

{-# INLINABLE equalsByteString #-}
-- | Check if two 'ByteString's are equal.
equalsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
equalsByteString x y = fromBuiltin (BI.equalsByteString x y)

{-# INLINABLE lessThanByteString #-}
-- | Check if one 'ByteString' is less than another.
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanByteString x y = fromBuiltin (BI.lessThanByteString x y)

{-# INLINABLE lessThanEqualsByteString #-}
-- | Check if one 'ByteString' is less than or equal to another.
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanEqualsByteString x y = fromBuiltin (BI.lessThanEqualsByteString x y)

{-# INLINABLE greaterThanByteString #-}
-- | Check if one 'ByteString' is greater than another.
greaterThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanByteString x y = BI.ifThenElse (BI.lessThanEqualsByteString x y) False True

{-# INLINABLE greaterThanEqualsByteString #-}
-- | Check if one 'ByteString' is greater than another.
greaterThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanEqualsByteString x y = BI.ifThenElse (BI.lessThanByteString x y) False True

{-# INLINABLE decodeUtf8 #-}
-- | Converts a ByteString to a String.
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 = BI.decodeUtf8

{-# INLINEABLE verifyEcdsaSecp256k1Signature #-}
-- | Given an ECDSA SECP256k1 verification key, an ECDSA SECP256k1 signature,
-- and an ECDSA SECP256k1 message hash (all as 'BuiltinByteString's), verify the
-- hash with that key and signature.
--
-- = Important note
--
-- The verification key, the signature, and the message hash must all be of
-- appropriate form and length. This function will error if any of
-- these are not the case.
verifyEcdsaSecp256k1Signature
  :: BuiltinByteString -- ^ Verification key (64 bytes)
  -> BuiltinByteString -- ^ Message hash (32 bytes)
  -> BuiltinByteString -- ^ Signature (64 bytes)
  -> Bool
verifyEcdsaSecp256k1Signature vk msg sig =
  fromBuiltin (BI.verifyEcdsaSecp256k1Signature vk msg sig)

{-# INLINEABLE verifySchnorrSecp256k1Signature #-}
-- | Given a Schnorr SECP256k1 verification key, a Schnorr SECP256k1 signature,
-- and a message (all as 'BuiltinByteString's), verify the message with that key
-- and signature.
--
-- = Important note
--
-- The verification key and signature must all be of appropriate form and
-- length. This function will error if this is not the case.
verifySchnorrSecp256k1Signature
  :: BuiltinByteString -- ^ Verification key (64 bytes)
  -> BuiltinByteString -- ^ Message
  -> BuiltinByteString -- ^ Signature (64 bytes)
  -> Bool
verifySchnorrSecp256k1Signature vk msg sig =
  fromBuiltin (BI.verifySchnorrSecp256k1Signature vk msg sig)

-- | Converts an 'Integer' into its 'BuiltinByteString' representation.
--
-- = Notes
--
-- Throughout, let @maxInteger@ be the maximum function for 'Integer's,
-- and @absInteger@ be the absolute value function for 'Integer's.
-- We define @zeroes :: 'Integer' -> 'BuiltinByteString'@ be the
-- function which, given input @i@, produces a 'BuiltinByteString' @bs@ such
-- that:
--
-- * @'lengthByteString' bs@ @=@ @'maxInteger' 0 i@; and
-- * For all @j :: 'Integer'@ such that @'greaterThanEqualsInteger' j 0@,
-- @'indexByteString' bs j = 0@;
--
-- We define @ones :: 'Integer' -> 'BuiltinByteString'@ identically to @zeroes@,
-- except that @'indexByteString' bs j = 255@ instead.
--
-- == Laws
--
-- 'integerToByteString' must roundtrip via 'byteStringToInteger'. Specifically,
-- for all @i :: 'Integer'@, we must have:
--
-- @'byteStringToInteger '.' 'integerToByteString' '$' i@ @=@ @i@
--
-- Furthermore, the length of any result of 'integerToByteString' must be
-- strictly positive:
--
-- @'greaterThanInteger' ('lengthByteString' '.' 'integerToByteString' i) 0@ @=@
-- @True@
--
-- Lastly, the result /must/ be encoded as defined in the Encoding section
-- below.
--
-- == Encoding
--
-- 'integerToByteString' follows the encoding we describe below; let @i ::
-- 'Integer'@. If @i@ is zero, @'integerToByteString' i@ @=@ @zeroes 1@;
-- we call this the /zero representation/. If @i@ is non-zero, the encoding
-- depends on the sign of @i@.
--
-- If @i@ is positive, @'integerToByteString' i@ @=@ @bs@ such that the
-- following hold:
--
-- * @'greaterThanInteger' ('byteStringLength' bs) 0@ @=@ @True@;
-- * Let @polyQuotientInteger :: 'Integer' -> 'Integer' ->
-- 'Integer' -> 'Integer'@ be defined such that
-- @polyQuotientInteger i j reps@ be a repeat application of 'quotientInteger'
-- with @j@ as its second argument @'maxInteger' 0 reps@ times to @i@. Let
-- @ix :: 'BuiltinInteger'@ such that @'greaterThanEqualsInteger' ix 0@ and
-- @'lessThanInteger' ix k@. Then, @'indexByteString' bs ix@ @=@
-- @'remainderInteger' (polyQuotientInteger i 256 ('subtractInteger' ('subtractInteger' k 1) ix)) 256@
--
-- We call this a /positive representation/.
--
-- If @i@ is negative, there are two cases:
--
-- * If the absolute value of @i@ is /not/ an exact power of 256, then
-- @'integerToByteString' i@ is the [two's
-- complement](https://en.wikipedia.org/wiki/Two%27s_complement) of the positive
-- representation of @'absInteger' i@.
-- * Otherwise, let @bs@ be the two's complement of the positive representation
-- of @'absInteger' i@. Then, @'integerToByteString' i@ is @'appendByteString'
-- (ones 1) bs@.
--
-- We call this a /negative representation/. We need to introduce the special
-- second case (with the \'ones padding\') for negative representations as exact
-- powers of 256 are their own two's complement: thus, we have to distinguish
-- positive cases from negative ones. We choose to do this by \'padding\', as
-- this makes the decode direction easier.
{-# INLINEABLE integerToByteString #-}
integerToByteString :: Integer -> BuiltinByteString
integerToByteString i = BI.integerToByteString (toBuiltin i)

-- | Converts a 'BuiltinByteString' into its 'Integer' representation.
--
-- = Notes
--
-- We inherit all definitions described for 'integerToByteString'.
--
-- == Laws
--
-- In addition to the roundtrip requirements specified by the laws of
-- 'integerToByteString', we also add the following requirements. Throughout,
-- let @i :: Integer@ and @j :: Integer@ such that @'greaterThanInteger' j 0@.
--
-- * /Padding/: If @bs@ is a zero representation or
-- a positive representation, then @'byteStringToInteger' bs@ @=@
-- @'byteStringToInteger' ('appendByteString' (zeroes i) bs)@; otherwise,
-- @'byteStringToInteger' bs@ @=@ @'byteStringToInteger' ('appendByteString'
-- (ones i) bs)@.
-- * /Zero homogeneity/: @'byteStringToInteger' (zeroes i)@ @=@ @0@.
-- * /One homogeneity/: @'byteStringToInteger' (ones j)@ @=@ @(-1)@.
--
-- A theorem of zero homogeneity is that @'byteStringToInteger' ""@ @=@ @0@.
--
-- == Redundant encodings
--
-- Unfortunately, the padding, zero homogeneity and one homogeneity laws mean
-- that the combination of 'byteStringToInteger' and 'integerToByteString'
-- cannot be an isomorphism. This is unavoidable: we either have to make
-- 'byteStringToInteger' partial, or allow redundant encodings. We chose the
-- second option as it is harmless, and as long as 'integerToByteString'
-- produces non-redundant encodings, shouldn't cause issues.
{-# INLINEABLE byteStringToInteger #-}
byteStringToInteger :: BuiltinByteString -> Integer
byteStringToInteger bs = fromBuiltin (BI.byteStringToInteger bs)

-- | If given arguments of identical length, constructs their bitwise logical
-- AND, erroring otherwise.
--
-- = Notes
--
-- We inherit all definitions described for 'integerToByteString'.
--
-- == Laws
--
-- 'andByteString' follows these laws:
--
-- * /Commutativity/: @'andByteString' bs1 bs2@ @=@ @'andByteString' bs2 bs1@
-- * /Associativity/: @'andByteString' bs1 ('andByteString' bs2 bs3)@ @=@
-- @'andByteString' ('andByteString' bs1 bs2) bs3@
-- * /Identity/: @'andByteString' bs (ones '.' 'lengthByteString' '$' bs)@ @=@
-- @bs@
-- * /Absorbtion/: @'andByteString' bs (zeroes '.' 'lengthByteString' '$' bs)@
-- @=@ @zeroes '.' 'lengthByteString' '$' bs@
-- * /De Morgan's law for AND/: @'complementByteString' ('andByteString' bs1
-- bs2)@ @=@ @'iorByteString' ('complementByteString' bs1)
-- ('complementByteString' bs2)@
-- * /Idempotence/: @'andByteString' bs bs@ @=@ @bs@
{-# INLINEABLE andByteString #-}
andByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
andByteString = BI.andByteString

-- | If given arguments of identical length, constructs their bitwise logical
-- IOR, erroring otherwise.
--
-- = Notes
--
-- We inherit all definitions described for 'integerToByteString'.
--
-- == Laws
--
-- 'iorByteString' follows these laws:
--
-- * /Commutativity/: @'iorByteString' bs1 bs2@ @=@ @'iorByteString' bs2 bs1@
-- * /Associativity/: @'iorByteString' bs1 ('iorByteString' bs2 bs3)@ @=@
-- @'iorByteString' ('iorByteString' bs1 bs2) bs3@
-- * /Identity/: @'iorByteString' bs (zeroes '.' 'lengthByteString' '$' bs)@ @=@
-- @bs@
-- * /Absorbtion/: @'iorByteString' bs (ones '.' 'lengthByteString' '$' bs)@
-- @=@ @ones '.' 'lengthByteString' '$' bs@
-- * /De Morgan's law for IOR/: @'complementByteString' ('iorByteString' bs1
-- bs2)@ @=@ @'andByteString' ('complementByteString' bs1)
-- ('complementByteString' bs2)@
-- * /Idempotence/: @'iorByteString' bs bs@ @=@ @bs@
{-# INLINEABLE iorByteString #-}
iorByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
iorByteString = BI.iorByteString

-- | If given arguments of identical length, constructs their bitwise logical
-- XOR, erroring otherwise.
--
-- = Notes
--
-- We inherit all definitions described for 'integerToByteString'.
--
-- == Laws
--
-- 'xorByteString' follows these laws:
--
-- * /Commutativity/: @'xorByteString' bs1 bs2@ @=@ @'xorByteString' bs2 bs1@
-- * /Associativity/: @'xorByteString' bs1 ('xorByteString' bs2 bs3)@ @=@
-- @'xorByteString' ('xorByteString' bs1 bs2) bs3@
-- * /Identity/: @'xorByteString' bs (zeroes '.' 'lengthByteString' '$' bs)@ @=@
-- @bs@
-- * /Complementarity/: @'xorByteString' bs (ones '.' 'lengthByteString' '$'
-- bs)@ @=@ @'complementByteString' bs@
-- * /Self-absorbtion/: @'xorByteString' bs bs@ @=@ @zeroes '.'
-- 'lengthByteString' '$' bs@
{-# INLINEABLE xorByteString #-}
xorByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
xorByteString = BI.xorByteString

-- | Constructs the [one's complement](https://en.wikipedia.org/wiki/Ones%27_complement)
-- of its argument.
--
-- = Laws
--
-- `complementByteString` is self-inverting: specifically, we have
-- @'complementByteString' '.' 'complementByteString' '$' bs@ @=@ @bs@.
{-# INLINEABLE complementByteString #-}
complementByteString :: BuiltinByteString -> BuiltinByteString
complementByteString = BI.complementByteString

-- | Shifts the 'BuiltinByteString' argument. More precisely, constructs a new
-- 'BuiltinByteString' by \'adjusting\' the bit indexes of the
-- 'BuiltinByteString' argument by the 'Integer' argument; if this would cause
-- an \'out-of-bounds\', that bit is 0 instead.
--
-- = Notes
--
-- We inherit all definitions described for 'integerToByteString'.
--
-- == Laws
--
-- 'shiftByteString' follows these laws:
--
-- * /Identity/: @'shiftByteString' bs 0@ @=@ @bs@
-- * /Decomposition/: Let @i, j :: 'Integer'@ such that either at least one of
-- @i@, @j@ is zero or @i@ and @j@ have the same sign. Then @'shiftByteString'
-- bs ('addInteger' i j)@ @=@ @'shiftByteString' ('shiftByteString' bs i) j@
-- * /Erasure/: If @greaterThanEqualsInteger ('absInteger' i) '.' 'lengthByteString' '$' bs@,
-- then @'shiftByteString' bs i@ @=@ @zeroes '.' 'lengthByteString' '$' bs@
{-# INLINEABLE shiftByteString #-}
shiftByteString :: BuiltinByteString -> Integer -> BuiltinByteString
shiftByteString bs i = BI.shiftByteString bs (toBuiltin i)

-- | Rotates the 'BuiltinByteString' argument. More precisely, constructs a new
-- 'BuiltinByteString' by \'adjusting\' the bit indexes of the
-- 'BuiltinByteString' argument by the 'Integer' argument; if this would cause
-- an \'out-of-bounds\', we \'wrap around\'.
--
-- = Laws
--
-- 'rotateByteString' follows these laws:
--
-- * /Identity/: @'rotateByteString' bs 0@ @=@ @bs@
-- * /Decomposition/: @'rotateByteString' bs ('addInteger' i j)@ @=@
-- @'rotateByteString' ('rotateByteString' bs i) j@
-- * /Wraparound/: Let @i :: Integer@ be nonzero. Then @'rotateByteString' bs i@
-- @=@ @'rotateByteString' bs ('remainderInteger' i ('timesInteger' 8 '.'
-- 'lengthByteString' '$' bs))@
{-# INLINEABLE rotateByteString #-}
rotateByteString :: BuiltinByteString -> Integer -> BuiltinByteString
rotateByteString bs i = BI.rotateByteString bs (toBuiltin i)

-- | Counts the number of 1 bits in the argument.
--
-- = Laws
--
-- 'popCountByteString' follows these laws:
--
-- * @'popCountByteString' ""@ @=@ @0@
-- * @'popCountByteString' ('appendByteString' bs1 bs2)@ @=@
-- @'addInteger' ('popCountByteString' bs1) ('popCountByteString' bs2)@
{-# INLINEABLE popCountByteString #-}
popCountByteString :: BuiltinByteString -> Integer
popCountByteString bs = fromBuiltin (BI.popCountByteString bs)

-- | Bitwise indexing operation. Errors when given an index that's not
-- in-bounds: specifically, indexes that are either negative or greater than or
-- equal to the number of bits in the 'BuiltinByteString' argument.
{-# INLINEABLE testBitByteString #-}
testBitByteString :: BuiltinByteString -> Integer -> Bool
testBitByteString bs i = fromBuiltin (BI.testBitByteString bs (toBuiltin i))

-- | Bitwise modification at an index. Errors when given an index that's not
-- in-bounds: specifically, indexes that are either negative or greater than
-- or equal to the number of bits in the 'BuiltinByteString' argument.
{-# INLINEABLE writeBitByteString #-}
writeBitByteString :: BuiltinByteString -> Integer -> Bool -> BuiltinByteString
writeBitByteString bs i b = BI.writeBitByteString bs (toBuiltin i) (toBuiltin b)

-- | Finds the lowest bit index such that 'testBitByteString' at that index is
-- 'True'. Returns @-1@ if no such index exists: that is, the
-- 'BuiltinByteString' argument has only zero bytes in it, or is empty.
{-# INLINEABLE findFirstSetByteString #-}
findFirstSetByteString :: BuiltinByteString -> Integer
findFirstSetByteString bs = fromBuiltin (BI.findFirstSetByteString bs)

{-# INLINABLE addInteger #-}
-- | Add two 'Integer's.
addInteger :: Integer -> Integer -> Integer
addInteger x y = fromBuiltin (BI.addInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE subtractInteger #-}
-- | Subtract two 'Integer's.
subtractInteger :: Integer -> Integer -> Integer
subtractInteger x y = fromBuiltin (BI.subtractInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE multiplyInteger #-}
-- | Multiply two 'Integer's.
multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger x y = fromBuiltin (BI.multiplyInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE divideInteger #-}
-- | Divide two integers.
divideInteger :: Integer -> Integer -> Integer
divideInteger x y = fromBuiltin (BI.divideInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE modInteger #-}
-- | Integer modulo operation.
modInteger :: Integer -> Integer -> Integer
modInteger x y = fromBuiltin (BI.modInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE quotientInteger #-}
-- | Quotient of two integers.
quotientInteger :: Integer -> Integer -> Integer
quotientInteger x y = fromBuiltin (BI.quotientInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE remainderInteger #-}
-- | Take the remainder of dividing two 'Integer's.
remainderInteger :: Integer -> Integer -> Integer
remainderInteger x y = fromBuiltin (BI.remainderInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE greaterThanInteger #-}
-- | Check whether one 'Integer' is greater than another.
greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger x y = BI.ifThenElse (BI.lessThanEqualsInteger x y ) False True

{-# INLINABLE greaterThanEqualsInteger #-}
-- | Check whether one 'Integer' is greater than or equal to another.
greaterThanEqualsInteger :: Integer -> Integer -> Bool
greaterThanEqualsInteger x y = BI.ifThenElse (BI.lessThanInteger x y) False True

{-# INLINABLE lessThanInteger #-}
-- | Check whether one 'Integer' is less than another.
lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger x y = fromBuiltin (BI.lessThanInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE lessThanEqualsInteger #-}
-- | Check whether one 'Integer' is less than or equal to another.
lessThanEqualsInteger :: Integer -> Integer -> Bool
lessThanEqualsInteger x y = fromBuiltin (BI.lessThanEqualsInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE equalsInteger #-}
-- | Check if two 'Integer's are equal.
equalsInteger :: Integer -> Integer -> Bool
equalsInteger x y = fromBuiltin (BI.equalsInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE error #-}
-- | Aborts evaluation with an error.
error :: () -> a
error x = BI.error (toBuiltin x)

{-# INLINABLE appendString #-}
-- | Append two 'String's.
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString = BI.appendString

{-# INLINABLE emptyString #-}
-- | An empty 'String'.
emptyString :: BuiltinString
emptyString = BI.emptyString

{-# INLINABLE equalsString #-}
-- | Check if two strings are equal
equalsString :: BuiltinString -> BuiltinString -> Bool
equalsString x y = fromBuiltin (BI.equalsString x y)

{-# INLINABLE showInteger #-}
showInteger :: Integer -> BuiltinString
showInteger = BI.showInteger

{-# INLINABLE showBool #-}
showBool :: Bool -> BuiltinString
showBool = BI.showBool

{-# INLINABLE showString #-}
showString :: BuiltinString -> BuiltinString
showString = BI.showString

{-# INLINABLE showByteString #-}
showByteString :: BuiltinByteString -> BuiltinString
showByteString = BI.showByteString

{-# INLINABLE showData #-}
showData :: BuiltinData -> BuiltinString
showData = BI.showData

{-# INLINABLE trace #-}
-- | Emit the given string as a trace message before evaluating the argument.
trace :: BuiltinString -> a -> a
trace = BI.trace

{-# INLINABLE encodeUtf8 #-}
-- | Convert a String into a ByteString.
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 = BI.encodeUtf8

matchList :: forall a r . BI.BuiltinList a -> r -> (a -> BI.BuiltinList a -> r) -> r
matchList l nilCase consCase = BI.chooseList l (const nilCase) (\_ -> consCase (BI.head l) (BI.tail l)) ()

{-# INLINABLE chooseData #-}
-- | Given five values for the five different constructors of 'BuiltinData', selects
-- one depending on which corresponds to the actual constructor of the given value.
chooseData :: forall a . BuiltinData -> a -> a -> a -> a -> a -> a
chooseData = BI.chooseData

{-# INLINABLE serialiseData #-}
-- | Convert a String into a ByteString.
serialiseData :: BuiltinData -> BuiltinByteString
serialiseData = BI.serialiseData

{-# INLINABLE mkConstr #-}
-- | Constructs a 'BuiltinData' value with the @Constr@ constructor.
mkConstr :: Integer -> [BuiltinData] -> BuiltinData
mkConstr i args = BI.mkConstr (toBuiltin i) (toBuiltin args)

{-# INLINABLE mkMap #-}
-- | Constructs a 'BuiltinData' value with the @Map@ constructor.
mkMap :: [(BuiltinData, BuiltinData)] -> BuiltinData
mkMap es = BI.mkMap (toBuiltin es)

{-# INLINABLE mkList #-}
-- | Constructs a 'BuiltinData' value with the @List@ constructor.
mkList :: [BuiltinData] -> BuiltinData
mkList l = BI.mkList (toBuiltin l)

{-# INLINABLE mkI #-}
-- | Constructs a 'BuiltinData' value with the @I@ constructor.
mkI :: Integer -> BuiltinData
mkI = BI.mkI

{-# INLINABLE mkB #-}
-- | Constructs a 'BuiltinData' value with the @B@ constructor.
mkB :: BuiltinByteString -> BuiltinData
mkB = BI.mkB

{-# INLINABLE unsafeDataAsConstr #-}
-- | Deconstructs a 'BuiltinData' as a @Constr@, or fails if it is not one.
unsafeDataAsConstr :: BuiltinData -> (Integer, [BuiltinData])
unsafeDataAsConstr d = fromBuiltin (BI.unsafeDataAsConstr d)

{-# INLINABLE unsafeDataAsMap #-}
-- | Deconstructs a 'BuiltinData' as a @Map@, or fails if it is not one.
unsafeDataAsMap :: BuiltinData -> [(BuiltinData, BuiltinData)]
unsafeDataAsMap d = fromBuiltin (BI.unsafeDataAsMap d)

{-# INLINABLE unsafeDataAsList #-}
-- | Deconstructs a 'BuiltinData' as a @List@, or fails if it is not one.
unsafeDataAsList :: BuiltinData -> [BuiltinData]
unsafeDataAsList d = fromBuiltin (BI.unsafeDataAsList d)

{-# INLINABLE unsafeDataAsI #-}
-- | Deconstructs a 'BuiltinData' as an @I@, or fails if it is not one.
unsafeDataAsI :: BuiltinData -> Integer
unsafeDataAsI d = fromBuiltin (BI.unsafeDataAsI d)

{-# INLINABLE unsafeDataAsB #-}
-- | Deconstructs a 'BuiltinData' as a @B@, or fails if it is not one.
unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB = BI.unsafeDataAsB

{-# INLINABLE equalsData #-}
-- | Check if two 'BuiltinData's are equal.
equalsData :: BuiltinData -> BuiltinData -> Bool
equalsData d1 d2 = fromBuiltin (BI.equalsData d1 d2)

{-# INLINABLE matchData #-}
-- | Given a 'BuiltinData' value and matching functions for the five constructors,
-- applies the appropriate matcher to the arguments of the constructor and returns the result.
matchData
    :: BuiltinData
    -> (Integer -> [BuiltinData] -> r)
    -> ([(BuiltinData, BuiltinData)] -> r)
    -> ([BuiltinData] -> r)
    -> (Integer -> r)
    -> (BuiltinByteString -> r)
    -> r
matchData d constrCase mapCase listCase iCase bCase =
   chooseData
   d
   (\_ -> uncurry constrCase (unsafeDataAsConstr d))
   (\_ -> mapCase (unsafeDataAsMap d))
   (\_ -> listCase (unsafeDataAsList d))
   (\_ -> iCase (unsafeDataAsI d))
   (\_ -> bCase (unsafeDataAsB d))
   ()

{-# INLINABLE matchData' #-}
-- | Given a 'BuiltinData' value and matching functions for the five constructors,
-- applies the appropriate matcher to the arguments of the constructor and returns the result.
matchData'
    :: BuiltinData
    -> (Integer -> BI.BuiltinList BuiltinData -> r)
    -> (BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> r)
    -> (BI.BuiltinList BuiltinData -> r)
    -> (Integer -> r)
    -> (BuiltinByteString -> r)
    -> r
matchData' d constrCase mapCase listCase iCase bCase =
   chooseData
   d
   (\_ -> let tup = BI.unsafeDataAsConstr d in constrCase (BI.fst tup) (BI.snd tup))
   (\_ -> mapCase (BI.unsafeDataAsMap d))
   (\_ -> listCase (BI.unsafeDataAsList d))
   (\_ -> iCase (unsafeDataAsI d))
   (\_ -> bCase (unsafeDataAsB d))
   ()
