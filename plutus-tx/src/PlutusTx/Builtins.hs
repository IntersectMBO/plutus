-- editorconfig-checker-disable-file

-- | Primitive names and functions for working with Plutus Core builtins.
module PlutusTx.Builtins
  ( -- * Bytestring builtins
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
  , blake2b_224
  , blake2b_256
  , keccak_256
  , ripemd_160
  , verifyEd25519Signature
  , verifyEcdsaSecp256k1Signature
  , verifySchnorrSecp256k1Signature
  , decodeUtf8
  , BuiltinByteStringHex (..)
  , BuiltinByteStringUtf8 (..)

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
  , expModInteger
  , BI.caseInteger

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

    -- * Pairs
  , pairToPair
  , BI.casePair

    -- * Lists
  , mkNil
  , mkNilOpaque
  , null
  , BI.caseList'
  , caseList
  , matchList
  , matchList'
  , headMaybe
  , BI.head
  , BI.tail
  , BI.drop
  , uncons
  , unsafeUncons

    -- * Arrays
  , BI.BuiltinArray
  , BI.listToArray
  , sopListToArray
  , BI.lengthOfArray
  , BI.indexArray

    -- * Tracing
  , trace

    -- * BLS12_381
  , BuiltinBLS12_381_G1_Element
  , bls12_381_G1_equals
  , bls12_381_G1_add
  , bls12_381_G1_scalarMul
  , bls12_381_G1_multiScalarMul
  , bls12_381_G1_neg
  , bls12_381_G1_compress
  , bls12_381_G1_uncompress
  , bls12_381_G1_hashToGroup
  , bls12_381_G1_compressed_zero
  , bls12_381_G1_compressed_generator
  , BuiltinBLS12_381_G2_Element
  , bls12_381_G2_equals
  , bls12_381_G2_add
  , bls12_381_G2_scalarMul
  , bls12_381_G2_multiScalarMul
  , bls12_381_G2_neg
  , bls12_381_G2_compress
  , bls12_381_G2_uncompress
  , bls12_381_G2_hashToGroup
  , bls12_381_G2_compressed_zero
  , bls12_381_G2_compressed_generator
  , BuiltinBLS12_381_MlResult
  , bls12_381_millerLoop
  , bls12_381_mulMlResult
  , bls12_381_finalVerify

    -- * Conversions
  , fromOpaque
  , toOpaque
  , useToOpaque
  , useFromOpaque
  , fromBuiltin
  , toBuiltin

    -- * Logical
  , ByteOrder (..)
  , integerToByteString
  , byteStringToInteger
  , andByteString
  , orByteString
  , xorByteString
  , complementByteString
  , readBit
  , writeBits
  , replicateByte

    -- * Bitwise
  , shiftByteString
  , rotateByteString
  , countSetBits
  , findFirstSetBit

    -- * Value
  , BI.insertCoin
  , BI.lookupCoin
  , BI.unionValue
  , BI.valueContains
  , BI.mkValue
  , BI.unsafeDataAsValue
  , BI.scaleValue
  ) where

import Data.Maybe
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.HasBuiltin
import PlutusTx.Builtins.HasOpaque
import PlutusTx.Builtins.Internal
  ( BuiltinBLS12_381_G1_Element (..)
  , BuiltinBLS12_381_G2_Element (..)
  , BuiltinBLS12_381_MlResult (..)
  , BuiltinByteString (..)
  , BuiltinData
  , BuiltinString
  )
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Integer (Integer)

import GHC.ByteOrder (ByteOrder (BigEndian, LittleEndian))

-- | Concatenates two 'ByteString's.
appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString = BI.appendByteString
{-# INLINEABLE appendByteString #-}

-- | Adds a byte to the front of a 'ByteString'.
consByteString :: Integer -> BuiltinByteString -> BuiltinByteString
consByteString n bs = BI.consByteString (toOpaque n) bs
{-# INLINEABLE consByteString #-}

-- | Returns the substring of a 'ByteString' from index 'start' of length 'n'.
sliceByteString :: Integer -> Integer -> BuiltinByteString -> BuiltinByteString
sliceByteString start n bs = BI.sliceByteString (toOpaque start) (toOpaque n) bs
{-# INLINEABLE sliceByteString #-}

-- | Returns the length of a 'ByteString'.
lengthOfByteString :: BuiltinByteString -> Integer
lengthOfByteString = BI.lengthOfByteString
{-# INLINEABLE lengthOfByteString #-}

-- | Returns the byte of a 'ByteString' at index.
indexByteString :: BuiltinByteString -> Integer -> Integer
indexByteString b n = BI.indexByteString b (toOpaque n)
{-# INLINEABLE indexByteString #-}

-- | An empty 'ByteString'.
emptyByteString :: BuiltinByteString
emptyByteString = BI.emptyByteString
{-# INLINEABLE emptyByteString #-}

-- | The SHA2-256 hash of a 'ByteString'
sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 = BI.sha2_256
{-# INLINEABLE sha2_256 #-}

-- | The SHA3-256 hash of a 'ByteString'
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 = BI.sha3_256
{-# INLINEABLE sha3_256 #-}

-- | The BLAKE2B-224 hash of a 'ByteString'
blake2b_224 :: BuiltinByteString -> BuiltinByteString
blake2b_224 = BI.blake2b_224
{-# INLINEABLE blake2b_224 #-}

-- | The BLAKE2B-256 hash of a 'ByteString'
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 = BI.blake2b_256
{-# INLINEABLE blake2b_256 #-}

-- | The KECCAK-256 hash of a 'ByteString'
keccak_256 :: BuiltinByteString -> BuiltinByteString
keccak_256 = BI.keccak_256
{-# INLINEABLE keccak_256 #-}

-- | The RIPEMD-160 hash of a 'ByteString'
ripemd_160 :: BuiltinByteString -> BuiltinByteString
ripemd_160 = BI.ripemd_160
{-# INLINEABLE ripemd_160 #-}

{-| Ed25519 signature verification. Verify that the signature is a signature of
the message by the public key. This will fail if key or the signature are not
of the expected length. -}
verifyEd25519Signature
  :: BuiltinByteString
  -- ^ Public Key (32 bytes)
  -> BuiltinByteString
  -- ^ Message    (arbirtary length)
  -> BuiltinByteString
  -- ^ Signature  (64 bytes)
  -> Bool
verifyEd25519Signature pubKey message signature =
  fromOpaque (BI.verifyEd25519Signature pubKey message signature)
{-# INLINEABLE verifyEd25519Signature #-}

-- | Check if two 'ByteString's are equal.
equalsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
equalsByteString x y = fromOpaque (BI.equalsByteString x y)
{-# INLINEABLE equalsByteString #-}

-- | Check if one 'ByteString' is less than another.
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanByteString x y = fromOpaque (BI.lessThanByteString x y)
{-# INLINEABLE lessThanByteString #-}

-- | Check if one 'ByteString' is less than or equal to another.
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanEqualsByteString x y = fromOpaque (BI.lessThanEqualsByteString x y)
{-# INLINEABLE lessThanEqualsByteString #-}

-- | Check if one 'ByteString' is greater than another.
greaterThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanByteString x y = BI.ifThenElse (BI.lessThanEqualsByteString x y) False True
{-# INLINEABLE greaterThanByteString #-}

-- | Check if one 'ByteString' is greater than another.
greaterThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanEqualsByteString x y = BI.ifThenElse (BI.lessThanByteString x y) False True
{-# INLINEABLE greaterThanEqualsByteString #-}

-- | Converts a ByteString to a String.
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 = BI.decodeUtf8
{-# INLINEABLE decodeUtf8 #-}

{-| Given an ECDSA SECP256k1 verification key, an ECDSA SECP256k1 signature,
and an ECDSA SECP256k1 message hash (all as 'BuiltinByteString's), verify the
hash with that key and signature.

= Note

There are additional well-formation requirements for the arguments beyond
their length:

* The first byte of the public key must correspond to the sign of the /y/
coordinate: this is @0x02@ if /y/ is even, and @0x03@ otherwise.
* The remaining bytes of the public key must correspond to the /x/
coordinate, as a big-endian integer.
* The first 32 bytes of the signature must correspond to the big-endian
integer representation of _r_.
* The last 32 bytes of the signature must correspond to the big-endian
integer representation of _s_.

While this primitive /accepts/ a hash, any caller should only pass it hashes
that they computed themselves: specifically, they should receive the
/message/ from a sender and hash it, rather than receiving the /hash/ from
said sender. Failure to do so can be
[dangerous](https://bitcoin.stackexchange.com/a/81116/35586). Other than
length, we make no requirements of what hash gets used.

= See also

*
[@secp256k1_ec_pubkey_serialize@](https://github.com/bitcoin-core/secp256k1/blob/master/include/secp256k1.h#L394);
this implements the format for the verification key that we accept, given a
length argument of 33 and the @SECP256K1_EC_COMPRESSED@ flag.
*
[@secp256k1_ecdsa_serialize_compact@](https://github.com/bitcoin-core/secp256k1/blob/master/include/secp256k1.h#L487);
this implements the format for the signature that we accept. -}
verifyEcdsaSecp256k1Signature
  :: BuiltinByteString
  -- ^ Verification key (33 bytes)
  -> BuiltinByteString
  -- ^ Message hash (32 bytes)
  -> BuiltinByteString
  -- ^ Signature (64 bytes)
  -> Bool
verifyEcdsaSecp256k1Signature vk msg sig =
  fromOpaque (BI.verifyEcdsaSecp256k1Signature vk msg sig)
{-# INLINEABLE verifyEcdsaSecp256k1Signature #-}

{-| Given a Schnorr SECP256k1 verification key, a Schnorr SECP256k1 signature,
and a message (all as 'BuiltinByteString's), verify the message with that key
and signature.

= Note

There are additional well-formation requirements for the arguments beyond
their length. Throughout, we refer to co-ordinates of the point @R@.

* The bytes of the public key must correspond to the /x/ coordinate, as a
big-endian integer, as specified in BIP-340.
* The first 32 bytes of the signature must correspond to the /x/ coordinate,
as a big-endian integer, as specified in BIP-340.
* The last 32 bytes of the signature must correspond to the bytes of /s/, as
a big-endian integer, as specified in BIP-340.

= See also

* [BIP-340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)
*
[@secp256k1_xonly_pubkey_serialize@](https://github.com/bitcoin-core/secp256k1/blob/master/include/secp256k1_extrakeys.h#L61);
this implements the format for the verification key that we accept.
*
[@secp256k1_schnorrsig_sign@](https://github.com/bitcoin-core/secp256k1/blob/master/include/secp256k1_schnorrsig.h#L129);
this implements the signing logic for signatures this builtin can verify. -}
verifySchnorrSecp256k1Signature
  :: BuiltinByteString
  -- ^ Verification key (32 bytes)
  -> BuiltinByteString
  -- ^ Message (arbitrary length)
  -> BuiltinByteString
  -- ^ Signature (64 bytes)
  -> Bool
verifySchnorrSecp256k1Signature vk msg sig =
  fromOpaque (BI.verifySchnorrSecp256k1Signature vk msg sig)
{-# INLINEABLE verifySchnorrSecp256k1Signature #-}

-- | Add two 'Integer's.
addInteger :: Integer -> Integer -> Integer
addInteger x y = fromOpaque (BI.addInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE addInteger #-}

-- | Subtract two 'Integer's.
subtractInteger :: Integer -> Integer -> Integer
subtractInteger x y = fromOpaque (BI.subtractInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE subtractInteger #-}

-- | Multiply two 'Integer's.
multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger x y = fromOpaque (BI.multiplyInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE multiplyInteger #-}

-- | Divide two integers.
divideInteger :: Integer -> Integer -> Integer
divideInteger x y = fromOpaque (BI.divideInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE divideInteger #-}

-- | Integer modulo operation.
modInteger :: Integer -> Integer -> Integer
modInteger x y = fromOpaque (BI.modInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE modInteger #-}

-- | Quotient of two integers.
quotientInteger :: Integer -> Integer -> Integer
quotientInteger x y = fromOpaque (BI.quotientInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE quotientInteger #-}

-- | Take the remainder of dividing two 'Integer's.
remainderInteger :: Integer -> Integer -> Integer
remainderInteger x y = fromOpaque (BI.remainderInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE remainderInteger #-}

-- | Check whether one 'Integer' is greater than another.
greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger x y = BI.ifThenElse (BI.lessThanEqualsInteger x y) False True
{-# INLINEABLE greaterThanInteger #-}

-- | Check whether one 'Integer' is greater than or equal to another.
greaterThanEqualsInteger :: Integer -> Integer -> Bool
greaterThanEqualsInteger x y = BI.ifThenElse (BI.lessThanInteger x y) False True
{-# INLINEABLE greaterThanEqualsInteger #-}

-- | Check whether one 'Integer' is less than another.
lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger x y = fromOpaque (BI.lessThanInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE lessThanInteger #-}

-- | Check whether one 'Integer' is less than or equal to another.
lessThanEqualsInteger :: Integer -> Integer -> Bool
lessThanEqualsInteger x y = fromOpaque (BI.lessThanEqualsInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE lessThanEqualsInteger #-}

-- | Check if two 'Integer's are equal.
equalsInteger :: Integer -> Integer -> Bool
equalsInteger x y = fromOpaque (BI.equalsInteger (toOpaque x) (toOpaque y))
{-# INLINEABLE equalsInteger #-}

-- | Aborts evaluation with an error.
error :: () -> a
error x = BI.error (toOpaque x)
{-# INLINEABLE error #-}

-- | Append two 'String's.
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString = BI.appendString
{-# INLINEABLE appendString #-}

-- | An empty 'String'.
emptyString :: BuiltinString
emptyString = BI.emptyString
{-# INLINEABLE emptyString #-}

-- | Check if two strings are equal
equalsString :: BuiltinString -> BuiltinString -> Bool
equalsString x y = fromOpaque (BI.equalsString x y)
{-# INLINEABLE equalsString #-}

-- | Emit the given string as a trace message before evaluating the argument.
trace :: BuiltinString -> a -> a
trace = BI.trace
{-# INLINEABLE trace #-}

-- | Convert a String into a ByteString.
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 = BI.encodeUtf8
{-# INLINEABLE encodeUtf8 #-}

null :: forall a. BI.BuiltinList a -> Bool
null l = fromOpaque (BI.null l)
{-# INLINEABLE null #-}

caseList :: forall a r. (() -> r) -> (a -> BI.BuiltinList a -> r) -> BI.BuiltinList a -> r
-- See Note [Making arguments non-strict in case and match functions]
caseList ~nilCase ~consCase l = BI.caseList' nilCase (\x xs _ -> consCase x xs) l ()
{-# INLINEABLE caseList #-}

matchList :: forall a r. BI.BuiltinList a -> (() -> r) -> (a -> BI.BuiltinList a -> r) -> r
matchList l nilCase consCase = caseList nilCase consCase l
{-# INLINEABLE matchList #-}

matchList' :: forall a r. BI.BuiltinList a -> r -> (a -> BI.BuiltinList a -> r) -> r
matchList' l nilCase consCase = BI.caseList' nilCase consCase l
{-# INLINEABLE matchList' #-}

headMaybe :: BI.BuiltinList a -> Maybe a
headMaybe = BI.caseList' Nothing (\h _ -> Just h)
{-# INLINE headMaybe #-}

-- | Uncons a builtin list, failing if the list is empty, useful in patterns.
uncons :: BI.BuiltinList a -> Maybe (a, BI.BuiltinList a)
uncons = BI.caseList' Nothing (\h t -> Just (h, t))
{-# INLINE uncons #-}

-- | Uncons a builtin list, failing if the list is empty, useful in patterns.
unsafeUncons :: BI.BuiltinList a -> (a, BI.BuiltinList a)
unsafeUncons = BI.unsafeCaseList (,)
{-# INLINE unsafeUncons #-}

-- | Turn a builtin pair into a normal pair, useful in patterns.
pairToPair :: BI.BuiltinPair a b -> (a, b)
pairToPair tup = (BI.fst tup, BI.snd tup)
{-# INLINE pairToPair #-}

sopListToArray :: (HasToOpaque a arep, MkNil arep) => [a] -> BI.BuiltinArray arep
sopListToArray l = BI.listToArray (toOpaque l)
{-# INLINEABLE sopListToArray #-}

{-| Given five values for the five different constructors of 'BuiltinData', selects
one depending on which corresponds to the actual constructor of the given value. -}
chooseData :: forall a. BuiltinData -> a -> a -> a -> a -> a -> a
chooseData = BI.chooseData
{-# INLINEABLE chooseData #-}

-- | Convert a String into a ByteString.
serialiseData :: BuiltinData -> BuiltinByteString
serialiseData = BI.serialiseData
{-# INLINEABLE serialiseData #-}

-- | Constructs a 'BuiltinData' value with the @Constr@ constructor.
mkConstr :: Integer -> [BuiltinData] -> BuiltinData
mkConstr i args = BI.mkConstr (toOpaque i) (toOpaque args)
{-# INLINEABLE mkConstr #-}

-- | Constructs a 'BuiltinData' value with the @Map@ constructor.
mkMap :: [(BuiltinData, BuiltinData)] -> BuiltinData
mkMap es = BI.mkMap (toOpaque es)
{-# INLINEABLE mkMap #-}

-- | Constructs a 'BuiltinData' value with the @List@ constructor.
mkList :: [BuiltinData] -> BuiltinData
mkList l = BI.mkList (toOpaque l)
{-# INLINEABLE mkList #-}

-- | Constructs a 'BuiltinData' value with the @I@ constructor.
mkI :: Integer -> BuiltinData
mkI = BI.mkI
{-# INLINEABLE mkI #-}

-- | Constructs a 'BuiltinData' value with the @B@ constructor.
mkB :: BuiltinByteString -> BuiltinData
mkB = BI.mkB
{-# INLINEABLE mkB #-}

-- | Deconstructs a 'BuiltinData' as a @Constr@, or fails if it is not one.
unsafeDataAsConstr :: BuiltinData -> (Integer, [BuiltinData])
unsafeDataAsConstr d = fromOpaque (BI.unsafeDataAsConstr d)
{-# INLINEABLE unsafeDataAsConstr #-}

-- | Deconstructs a 'BuiltinData' as a @Map@, or fails if it is not one.
unsafeDataAsMap :: BuiltinData -> [(BuiltinData, BuiltinData)]
unsafeDataAsMap d = fromOpaque (BI.unsafeDataAsMap d)
{-# INLINEABLE unsafeDataAsMap #-}

-- | Deconstructs a 'BuiltinData' as a @List@, or fails if it is not one.
unsafeDataAsList :: BuiltinData -> [BuiltinData]
unsafeDataAsList d = fromOpaque (BI.unsafeDataAsList d)
{-# INLINEABLE unsafeDataAsList #-}

-- | Deconstructs a 'BuiltinData' as an @I@, or fails if it is not one.
unsafeDataAsI :: BuiltinData -> Integer
unsafeDataAsI d = fromOpaque (BI.unsafeDataAsI d)
{-# INLINEABLE unsafeDataAsI #-}

-- | Deconstructs a 'BuiltinData' as a @B@, or fails if it is not one.
unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB = BI.unsafeDataAsB
{-# INLINEABLE unsafeDataAsB #-}

-- | Check if two 'BuiltinData's are equal.
equalsData :: BuiltinData -> BuiltinData -> Bool
equalsData d1 d2 = fromOpaque (BI.equalsData d1 d2)
{-# INLINEABLE equalsData #-}

matchData'
  :: BuiltinData
  -> (Integer -> BI.BuiltinList BuiltinData -> r)
  -> (BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> r)
  -> (BI.BuiltinList BuiltinData -> r)
  -> (Integer -> r)
  -> (BuiltinByteString -> r)
  -> r
-- See Note [Making arguments non-strict in case and match functions]
matchData' d ~constrCase ~mapCase ~listCase ~iCase ~bCase =
  chooseData
    d
    (\_ -> BI.casePair (BI.unsafeDataAsConstr d) (\l r -> constrCase l r))
    (\_ -> mapCase (BI.unsafeDataAsMap d))
    (\_ -> listCase (BI.unsafeDataAsList d))
    (\_ -> iCase (unsafeDataAsI d))
    (\_ -> bCase (unsafeDataAsB d))
    ()
{-# INLINEABLE matchData' #-}

{-| Given a 'BuiltinData' value and matching functions for the five constructors,
applies the appropriate matcher to the arguments of the constructor and returns the result. -}
matchData
  :: BuiltinData
  -> (Integer -> [BuiltinData] -> r)
  -> ([(BuiltinData, BuiltinData)] -> r)
  -> ([BuiltinData] -> r)
  -> (Integer -> r)
  -> (BuiltinByteString -> r)
  -> r
-- See Note [Making arguments non-strict in case and match functions]
matchData d ~constrCase ~mapCase ~listCase ~iCase ~bCase =
  matchData'
    d
    (\i ds -> constrCase i (fromOpaque ds))
    (\ps -> mapCase (fromOpaque ps))
    (\ds -> listCase (fromOpaque ds))
    iCase
    bCase
{-# INLINEABLE matchData #-}

-- G1 --
bls12_381_G1_equals :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> Bool
bls12_381_G1_equals a b = fromOpaque (BI.bls12_381_G1_equals a b)
{-# INLINEABLE bls12_381_G1_equals #-}

bls12_381_G1_add
  :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_add = BI.bls12_381_G1_add
{-# INLINEABLE bls12_381_G1_add #-}

bls12_381_G1_scalarMul :: Integer -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_scalarMul = BI.bls12_381_G1_scalarMul
{-# INLINEABLE bls12_381_G1_scalarMul #-}

bls12_381_G1_multiScalarMul :: [Integer] -> [BuiltinBLS12_381_G1_Element] -> BuiltinBLS12_381_G1_Element
bls12_381_G1_multiScalarMul ints points = BI.bls12_381_G1_multiScalarMul (toOpaque ints) (toOpaque points)
{-# INLINEABLE bls12_381_G1_multiScalarMul #-}

bls12_381_G1_neg :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_neg = BI.bls12_381_G1_neg
{-# INLINEABLE bls12_381_G1_neg #-}

bls12_381_G1_compress :: BuiltinBLS12_381_G1_Element -> BuiltinByteString
bls12_381_G1_compress = BI.bls12_381_G1_compress
{-# INLINEABLE bls12_381_G1_compress #-}

bls12_381_G1_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_uncompress = BI.bls12_381_G1_uncompress
{-# INLINEABLE bls12_381_G1_uncompress #-}

bls12_381_G1_hashToGroup :: BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_hashToGroup = BI.bls12_381_G1_hashToGroup
{-# INLINEABLE bls12_381_G1_hashToGroup #-}

bls12_381_G1_compressed_zero :: BuiltinByteString
bls12_381_G1_compressed_zero = BI.bls12_381_G1_compressed_zero
{-# INLINEABLE bls12_381_G1_compressed_zero #-}

bls12_381_G1_compressed_generator :: BuiltinByteString
bls12_381_G1_compressed_generator = BI.bls12_381_G1_compressed_generator
{-# INLINEABLE bls12_381_G1_compressed_generator #-}

-- G2 --
bls12_381_G2_equals :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> Bool
bls12_381_G2_equals a b = fromOpaque (BI.bls12_381_G2_equals a b)
{-# INLINEABLE bls12_381_G2_equals #-}

bls12_381_G2_add
  :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_add = BI.bls12_381_G2_add
{-# INLINEABLE bls12_381_G2_add #-}

bls12_381_G2_scalarMul :: Integer -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_scalarMul = BI.bls12_381_G2_scalarMul
{-# INLINEABLE bls12_381_G2_scalarMul #-}

bls12_381_G2_multiScalarMul :: [Integer] -> [BuiltinBLS12_381_G2_Element] -> BuiltinBLS12_381_G2_Element
bls12_381_G2_multiScalarMul ints points = BI.bls12_381_G2_multiScalarMul (toOpaque ints) (toOpaque points)
{-# INLINEABLE bls12_381_G2_multiScalarMul #-}

bls12_381_G2_neg :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_neg = BI.bls12_381_G2_neg
{-# INLINEABLE bls12_381_G2_neg #-}

bls12_381_G2_compress :: BuiltinBLS12_381_G2_Element -> BuiltinByteString
bls12_381_G2_compress = BI.bls12_381_G2_compress
{-# INLINEABLE bls12_381_G2_compress #-}

bls12_381_G2_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_uncompress = BI.bls12_381_G2_uncompress
{-# INLINEABLE bls12_381_G2_uncompress #-}

bls12_381_G2_hashToGroup :: BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_hashToGroup = BI.bls12_381_G2_hashToGroup
{-# INLINEABLE bls12_381_G2_hashToGroup #-}

bls12_381_G2_compressed_zero :: BuiltinByteString
bls12_381_G2_compressed_zero = BI.bls12_381_G2_compressed_zero
{-# INLINEABLE bls12_381_G2_compressed_zero #-}

bls12_381_G2_compressed_generator :: BuiltinByteString
bls12_381_G2_compressed_generator = BI.bls12_381_G2_compressed_generator
{-# INLINEABLE bls12_381_G2_compressed_generator #-}

-- Pairing --
bls12_381_millerLoop
  :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_MlResult
bls12_381_millerLoop = BI.bls12_381_millerLoop
{-# INLINEABLE bls12_381_millerLoop #-}

bls12_381_mulMlResult
  :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult
bls12_381_mulMlResult = BI.bls12_381_mulMlResult
{-# INLINEABLE bls12_381_mulMlResult #-}

bls12_381_finalVerify :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> Bool
bls12_381_finalVerify a b = fromOpaque (BI.bls12_381_finalVerify a b)
{-# INLINEABLE bls12_381_finalVerify #-}

-- Bitwise conversions

-- The PLC builtins take a boolean argument to indicate the endianness of the
-- conversion, but here we use GHC.ByteOrder.ByteOrder for clarity.
byteOrderToBool :: ByteOrder -> Bool
byteOrderToBool BigEndian = True
byteOrderToBool LittleEndian = False
{-# INLINEABLE byteOrderToBool #-}

{-| Convert a 'BuiltinInteger' into a 'BuiltinByteString', as described in
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121).
The first argument indicates the endianness of the conversion and the third
argument is the integer to be converted, which must be non-negative.  The
second argument must also be non-negative and it indicates the required width
of the output.  If the width is zero then the output is the smallest
bytestring which can contain the converted input (and in this case, the
integer 0 encodes to the empty bytestring).  If the width is nonzero then the
output bytestring will be padded to the required width with 0x00 bytes (on
the left for big-endian conversions and on the right for little-endian
conversions); if the input integer is too big to fit into a bytestring of the
specified width then the conversion will fail.  Conversion will also fail if
the specified width is greater than 8192 or the input integer is too big to
fit into a bytestring of length 8192. -}
integerToByteString :: ByteOrder -> Integer -> Integer -> BuiltinByteString
integerToByteString endianness = BI.integerToByteString (toOpaque (byteOrderToBool endianness))
{-# INLINEABLE integerToByteString #-}

{-| Convert a 'BuiltinByteString' to a 'BuiltinInteger', as described in
[CIP-121](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121).
The first argument indicates the endianness of the conversion and the second
is the bytestring to be converted.  There is no limitation on the size of
the bytestring.  The empty bytestring is converted to the integer 0. -}
byteStringToInteger :: ByteOrder -> BuiltinByteString -> Integer
byteStringToInteger endianness =
  BI.byteStringToInteger (toOpaque (byteOrderToBool endianness))
{-# INLINEABLE byteStringToInteger #-}

-- Bitwise operations

{-| Shift a 'BuiltinByteString', as per
[CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123). -}
shiftByteString :: BuiltinByteString -> Integer -> BuiltinByteString
shiftByteString = BI.shiftByteString
{-# INLINEABLE shiftByteString #-}

{-| Rotate a 'BuiltinByteString', as per
[CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123). -}
rotateByteString :: BuiltinByteString -> Integer -> BuiltinByteString
rotateByteString = BI.rotateByteString
{-# INLINEABLE rotateByteString #-}

{-| Count the set bits in a 'BuiltinByteString', as per
[CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123). -}
countSetBits :: BuiltinByteString -> Integer
countSetBits = BI.countSetBits
{-# INLINEABLE countSetBits #-}

{-| Find the lowest index of a set bit in a 'BuiltinByteString', as per
[CIP-123](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123).

If given a 'BuiltinByteString' which consists only of zero bytes (including the empty
'BuiltinByteString', this returns @-1@. -}
findFirstSetBit :: BuiltinByteString -> Integer
findFirstSetBit = BI.findFirstSetBit
{-# INLINEABLE findFirstSetBit #-}

-- Logical operations

{-| Perform logical AND on two 'BuiltinByteString' arguments, as described in
[CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bitwiselogicaland).

The first argument indicates whether padding semantics should be used or not;
if 'False', truncation semantics will be used instead.

= See also

* [Padding and truncation
semantics](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#padding-versus-truncation-semantics)
* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme) -}
andByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
andByteString b = BI.andByteString (toOpaque b)
{-# INLINEABLE andByteString #-}

{-| Perform logical OR on two 'BuiltinByteString' arguments, as described
[here](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bitwiselogicalor).

The first argument indicates whether padding semantics should be used or not;
if 'False', truncation semantics will be used instead.

= See also

* [Padding and truncation
semantics](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#padding-versus-truncation-semantics)
* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme) -}
orByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
orByteString b = BI.orByteString (toOpaque b)
{-# INLINEABLE orByteString #-}

{-| Perform logical XOR on two 'BuiltinByteString' arguments, as described
[here](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bitwiselogicalxor).

The first argument indicates whether padding semantics should be used or not;
if 'False', truncation semantics will be used instead.

= See also

* [Padding and truncation
semantics](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#padding-versus-truncation-semantics)
* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme) -}
xorByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
xorByteString b = BI.xorByteString (toOpaque b)
{-# INLINEABLE xorByteString #-}

{-| Perform logical complement on a 'BuiltinByteString', as described
[here](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bitwiselogicalcomplement).

= See also

* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme) -}
complementByteString
  :: BuiltinByteString
  -> BuiltinByteString
complementByteString = BI.complementByteString
{-# INLINEABLE complementByteString #-}

{-| Read a bit at the _bit_ index given by the 'Integer' argument in the
'BuiltinByteString' argument. The result will be 'True' if the corresponding bit is set, and
'False' if it is clear. Will error if given an out-of-bounds index argument; that is, if the
index is either negative, or equal to or greater than the total number of bits in the
'BuiltinByteString' argument.

= See also

* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme)
* [Operation
description](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#readbit) -}
readBit
  :: BuiltinByteString
  -> Integer
  -> Bool
readBit bs i = fromOpaque (BI.readBit bs i)
{-# INLINEABLE readBit #-}

{-| Given a 'BuiltinByteString', a list of indexes to change, and a boolean
value 'b' to change those indexes to, set the /bit/ at each of the specified
index as follows:

* If 'b' is 'True', set that bit;
* Otherwise, clear that bit.

Will error if any of the indexes are out-of-bounds: that is, if the index is either negative, or
equal to or greater than the total number of bits in the 'BuiltinByteString' argument.

= Note

This differs slightly from the description of the [corresponding operation in
CIP-122](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#writebits);
instead of a single changelist argument comprised of pairs, we instead pass a
single list of indexes to change, and a single boolean value to change those
indexes to. The original proposal allowed one to set and clear bits in a
single operation, but constructing the list of boolean values for the updates
was somewhat expensive.  If it's really necessary to set some bits and clear
others then it is easier to call the function twice, once to set bits and
and once to clear them.

= See also

* [Bit indexing
scheme](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#bit-indexing-scheme)
* [Operation
description](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#writebits) -}
writeBits
  :: BuiltinByteString
  -> [Integer]
  -> Bool
  -> BuiltinByteString
writeBits bs ixes bit = BI.writeBits bs (toOpaque ixes) (toOpaque bit)
{-# INLINEABLE writeBits #-}

{-| Given a length (first argument) and a byte (second argument), produce a 'BuiltinByteString' of
that length, with that byte in every position. Will error if given a negative length, or a second
argument that isn't a byte (less than 0, greater than 255).

= See also

* [Operation
description](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122#replicateByteString) -}
replicateByte
  :: Integer
  -> Integer
  -> BuiltinByteString
replicateByte = BI.replicateByte
{-# INLINEABLE replicateByte #-}

{-| Modular exponentiation primitive, as defined in CIP-0109.

= See also

* [Operation
description](https://cips.cardano.org/cip/CIP-0109) -}
expModInteger
  :: Integer
  -> Integer
  -> Integer
  -> Integer
expModInteger = BI.expModInteger
{-# INLINEABLE expModInteger #-}
