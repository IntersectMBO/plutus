-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
-- This ensures that we don't put *anything* about these functions into the interface
-- file, otherwise GHC can be clever about the ones that are always error, even though
-- they're OPAQUE!
{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
-- See Note [Opaque builtin types]

{-| This module contains the special Haskell names that are used to map to builtin types or functions
  in Plutus Core.

  Most users should not use this module directly, but rather use 'PlutusTx.Builtins'.

  Please note that the documentation for each function will only include operational invariants
  if there are any. This documentation assumes that the type system correctly enforces and
  prevents any structural errors on the generated UPLC. See Note [Structural vs operational errors
  within builtins].

  Also note that all builtin functions will fail if the CEK machine exceeds its evaluation budget.
  Builtin functions with dynamic costing are particularly prone to budget overruns: for example,
  addInteger and appendByteString differ cost based on input size, so supplying very large integers or
  byte strings will cause these functions to abort when the budget limit is reached and fail.
  See Note [Budgeting]. -}
module PlutusTx.Builtins.Internal where

import Codec.Serialise
import Control.DeepSeq (NFData (..))
import Data.ByteArray qualified as BA
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Coerce (coerce)
import Data.Data (Data)
import Data.Foldable qualified as Foldable
import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.List qualified as Haskell
import Data.Text as Text (Text, empty)
import Data.Text.Encoding as Text (decodeUtf8, encodeUtf8)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import GHC.Generics (Generic)
import PlutusCore.Bitwise qualified as Bitwise
import PlutusCore.Builtin (BuiltinResult (..))
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Crypto.Ed25519 qualified
import PlutusCore.Crypto.ExpMod as ExpMod
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusCore.Crypto.Secp256k1 qualified
import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty (Pretty (..), display)
import PlutusCore.Value qualified as PLC
import PlutusCore.Value qualified as Value
import Prettyprinter (viaShow)

{-
We do not use qualified import because the whole module contains off-chain code
which is replaced later with on-chain implementations by the plutus-tx-plugin.
-}
import Prelude as Haskell

{- Note [Builtin name definitions]
The builtins here have definitions so they can be used in off-chain code too.

However they *must* be replaced by the compiler when used in Plutus Tx code, so
in particular they must *not* be inlined, otherwise we can't spot them to replace
them.
-}

{- Note [Delaying error]
The Plutus Core 'error' builtin is of type 'forall a . a', but the
one we expose here is of type 'forall a . () -> a'.

This is because it's hard to get the evaluation order right with
the non-delayed version - it's easy to end up with it getting thrown
unconditionally, or before some other effect (e.g. tracing). On the other
hand, it's much easier to work with the delayed version.

But why not just define that in the library? i.e.

    error = \_ -> Builtins.error

The answer is that GHC is eager to inline and reduce this function, which
does the Wrong Thing. We can't stop GHC doing this (at the moment), but
for most of our functions it's not a *semantic* problem. Here, however,
it is a problem. So we just expose the delayed version as the builtin.
-}

{- Note [Opaque builtin types]
We have some opaque types that we use to represent the Plutus builtin types
in Haskell.

We want them to be opaque so that our users don't do anything with them that
we can't handle, but also so that GHC doesn't look inside and try and get clever.

In particular, we need to use 'data' rather than 'newtype' even for simple wrappers,
otherwise GHC gets very keen to optimize through the newtype and e.g. our users
see 'Addr#' popping up everywhere.
-}

error :: BuiltinUnit -> a
error = Haskell.error "PlutusTx.Builtins.Internal.error"
{-# OPAQUE error #-}

{-
BOOL
-}

ifThenElse :: Bool -> a -> a -> a
ifThenElse b x y = if b then x else y
{-# OPAQUE ifThenElse #-}

{-
UNIT
-}

-- See Note [Opaque builtin types]
data BuiltinUnit = BuiltinUnit ~() deriving stock (Data)

-- | Unit
unitval :: BuiltinUnit
unitval = BuiltinUnit ()
{-# OPAQUE unitval #-}

chooseUnit :: BuiltinUnit -> a -> a
chooseUnit (BuiltinUnit ()) a = a
{-# OPAQUE chooseUnit #-}

{-
INTEGER
-}

-- I'm somewhat surprised that this works despite not being opaque! GHC doesn't seem to
-- mess with 'Integer', which is suspicious to me. Probably we *should* make 'BuiltinInteger'
-- opaque, but that's going to really mess with our users' code...
type BuiltinInteger = Integer

-- | Adds two integers and never fails.
addInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
addInteger = coerce ((+) @Integer)
{-# OPAQUE addInteger #-}

-- | Subtracts two integers and never fails.
subtractInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
subtractInteger = coerce ((-) @Integer)
{-# OPAQUE subtractInteger #-}

-- | Multiplies two integers and never fails.
multiplyInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
multiplyInteger = coerce ((*) @Integer)
{-# OPAQUE multiplyInteger #-}

{-| Finds the quotient of two integers and fails when the second argument, the divisor, is zero.
See Note [Integer division operations] for explanation on 'divideInteger', 'modInteger',
'quotientInteger', and 'remainderInteger'. -}
divideInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
divideInteger = coerce (div @Integer)
{-# OPAQUE divideInteger #-}

-- | Finds the remainder of two integers and fails when the second argument, the divisor, is zero.
modInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
modInteger = coerce (mod @Integer)
{-# OPAQUE modInteger #-}

-- | Finds the quotient of two integers and fails when the second argument, the divisor, is zero.
quotientInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
quotientInteger = coerce (quot @Integer)
{-# OPAQUE quotientInteger #-}

-- | Finds the remainder of two integers and fails when the second argument, the divisor, is zero.
remainderInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
remainderInteger = coerce (rem @Integer)
{-# OPAQUE remainderInteger #-}

{-| Compares two integers and returns true when the first argument is less than the second
| argument. -}
lessThanInteger :: BuiltinInteger -> BuiltinInteger -> Bool
lessThanInteger x y = coerce ((<) @Integer) x y
{-# OPAQUE lessThanInteger #-}

{-| Compares two integers and returns true when the first argument is less or equal to than the
| second argument. -}
lessThanEqualsInteger :: BuiltinInteger -> BuiltinInteger -> Bool
lessThanEqualsInteger x y = coerce ((<=) @Integer) x y
{-# OPAQUE lessThanEqualsInteger #-}

-- | Checks equality of two integers and never fails.
equalsInteger :: BuiltinInteger -> BuiltinInteger -> Bool
equalsInteger x y = coerce ((==) @Integer) x y
{-# OPAQUE equalsInteger #-}

{-
BYTESTRING
-}

-- See Note [Opaque builtin types]

-- | An opaque type representing Plutus Core ByteStrings.
data BuiltinByteString = BuiltinByteString ~BS.ByteString deriving stock (Data)

instance Haskell.Show BuiltinByteString where
  show (BuiltinByteString bs) = show bs
instance Haskell.Eq BuiltinByteString where
  (==) (BuiltinByteString bs) (BuiltinByteString bs') = (==) bs bs'
instance Haskell.Ord BuiltinByteString where
  compare (BuiltinByteString bs) (BuiltinByteString bs') = compare bs bs'
instance Haskell.Semigroup BuiltinByteString where
  (<>) (BuiltinByteString bs) (BuiltinByteString bs') = BuiltinByteString $ (<>) bs bs'
instance Haskell.Monoid BuiltinByteString where
  mempty = BuiltinByteString mempty
instance Hashable BuiltinByteString where
  hashWithSalt s (BuiltinByteString bs) = hashWithSalt s bs
instance Serialise BuiltinByteString where
  encode (BuiltinByteString bs) = encode bs
  decode = BuiltinByteString <$> decode
instance NFData BuiltinByteString where
  rnf (BuiltinByteString bs) = rnf bs
instance BA.ByteArrayAccess BuiltinByteString where
  length (BuiltinByteString bs) = BA.length bs
  withByteArray (BuiltinByteString bs) = BA.withByteArray bs
instance BA.ByteArray BuiltinByteString where
  allocRet i p = fmap (fmap BuiltinByteString) $ BA.allocRet i p

instance Pretty BuiltinByteString where
  pretty = viaShow

-- | Appends a bytestring to another and never fails.
appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinByteString $ BS.append b1 b2
{-# OPAQUE appendByteString #-}

{-| Appends a byte to the given bytestring.
  The semantics of this function differ based on [Builtin semantics variants].
  - For builtin semantics variant A and B, that is for PlutusV1 and PlutusV2, this reduces the first argument
    modulo 256 and will never fail.
  - For builtin semantics variant C, that is for PlutusV3, this will expect first argument to be in range
    @[0..255]@ and fail otherwise. -}
consByteString :: BuiltinInteger -> BuiltinByteString -> BuiltinByteString
consByteString n (BuiltinByteString b) = BuiltinByteString $ BS.cons (fromIntegral n) b
{-# OPAQUE consByteString #-}

{-| Slices the given bytestring and never fails. The first integer marks the beginning index and the
  second marks the end. Indices are expected to be 0-indexed, and when the first integer is greater
  than the second, it returns an empty bytestring. -}
sliceByteString :: BuiltinInteger -> BuiltinInteger -> BuiltinByteString -> BuiltinByteString
sliceByteString start n (BuiltinByteString b) = BuiltinByteString $ BS.take (fromIntegral n) (BS.drop (fromIntegral start) b)
{-# OPAQUE sliceByteString #-}

-- | Returns the length of the provided bytestring.
lengthOfByteString :: BuiltinByteString -> BuiltinInteger
lengthOfByteString (BuiltinByteString b) = toInteger $ BS.length b
{-# OPAQUE lengthOfByteString #-}

{-| Returns the n-th byte from the bytestring. Fails if the given index is not in the range @[0..j)@,
  where @j@ is the length of the bytestring. -}
indexByteString :: BuiltinByteString -> BuiltinInteger -> BuiltinInteger
indexByteString (BuiltinByteString b) i = toInteger $ BS.index b (fromInteger i)
{-# OPAQUE indexByteString #-}

-- | An empty bytestring.
emptyByteString :: BuiltinByteString
emptyByteString = BuiltinByteString BS.empty
{-# OPAQUE emptyByteString #-}

-- | Computes the SHA2-256 hash of the given bytestring.
sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha2_256 b
{-# OPAQUE sha2_256 #-}

-- | Computes the SHA3-256 hash of the given bytestring.
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha3_256 b
{-# OPAQUE sha3_256 #-}

-- | Computes the Blake2b-224 hash of the given bytestring.
blake2b_224 :: BuiltinByteString -> BuiltinByteString
blake2b_224 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_224 b
{-# OPAQUE blake2b_224 #-}

-- | Computes the Blake2b-256 hash of the given bytestring.
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_256 b
{-# OPAQUE blake2b_256 #-}

-- | Computes the Keccak-256 hash of the given bytestring.
keccak_256 :: BuiltinByteString -> BuiltinByteString
keccak_256 (BuiltinByteString b) = BuiltinByteString $ Hash.keccak_256 b
{-# OPAQUE keccak_256 #-}

-- | Computes the RIPEMD-160 hash of the given bytestring.
ripemd_160 :: BuiltinByteString -> BuiltinByteString
ripemd_160 (BuiltinByteString b) = BuiltinByteString $ Hash.ripemd_160 b
{-# OPAQUE ripemd_160 #-}

{-| Ed25519 signature verification. The first bytestring is the public key (32 bytes), followed
  by an arbitrary-size message and the signature (64 bytes). The sizes of the public
  key and signature are enforced, and it fails when given bytestrings of incorrect size. -}
verifyEd25519Signature :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> Bool
verifyEd25519Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Ed25519.verifyEd25519Signature vk msg sig of
    BuiltinSuccess b -> b
    BuiltinSuccessWithLogs logs b -> traceAll logs b
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "Ed25519 signature verification errored."
{-# OPAQUE verifyEd25519Signature #-}

{-| ECDSA signature verification on the SECP256k1 curve. The first bytestring is the public key (32 bytes),
  followed by the message hash (32 bytes) and the signature (64 bytes). The sizes of the public key and signature
  are enforced, and it fails when given bytestrings of incorrect size. -}
verifyEcdsaSecp256k1Signature
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
verifyEcdsaSecp256k1Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Secp256k1.verifyEcdsaSecp256k1Signature vk msg sig of
    BuiltinSuccess b -> b
    BuiltinSuccessWithLogs logs b -> traceAll logs b
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "ECDSA SECP256k1 signature verification errored."
{-# OPAQUE verifyEcdsaSecp256k1Signature #-}

{-| Schnorr signature verification on the SECP256k1 curve. The first bytestring is the public key (32 bytes),
  followed by an arbitrary-length message and the signature (64 bytes). The sizes of the public key and signature
  are enforced, and it fails when given bytestrings of incorrect size. -}
verifySchnorrSecp256k1Signature
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
  -> Bool
verifySchnorrSecp256k1Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Secp256k1.verifySchnorrSecp256k1Signature vk msg sig of
    BuiltinSuccess b -> b
    BuiltinSuccessWithLogs logs b -> traceAll logs b
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "Schnorr SECP256k1 signature verification errored."
{-# OPAQUE verifySchnorrSecp256k1Signature #-}

-- | Runs trace for each element in a foldable structure.
traceAll
  :: forall (a :: Type) (f :: Type -> Type)
   . Foldable f => f Text -> a -> a
traceAll logs x = Foldable.foldl' (\acc t -> trace (BuiltinString t) acc) x logs

-- | Checks the equality of two bytestrings and never fails
equalsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
equalsByteString (BuiltinByteString b1) (BuiltinByteString b2) = b1 == b2
{-# OPAQUE equalsByteString #-}

{-| Checks if the first bytestring is less than the second bytestring and never fails. Comparison of the
  bytestrings will behave identically to the 'compare' implementation in 'ByteString.Ord'. It will compare
  two bytestrings byte by byte—lexicographical ordering. -}
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanByteString (BuiltinByteString b1) (BuiltinByteString b2) = b1 < b2
{-# OPAQUE lessThanByteString #-}

-- | Checks if the first bytestring is less than or equal to the second bytestring and never fails.
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanEqualsByteString (BuiltinByteString b1) (BuiltinByteString b2) = b1 <= b2
{-# OPAQUE lessThanEqualsByteString #-}

-- | Decodes the given bytestring to a string and fails when the given bytestring is not a valid UTF-8 bytestring.
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 (BuiltinByteString b) = BuiltinString $ Text.decodeUtf8 b
{-# OPAQUE decodeUtf8 #-}

{-
STRING
-}

-- See Note [Opaque builtin types]
data BuiltinString = BuiltinString ~Text deriving stock (Data)

instance Haskell.Show BuiltinString where
  show (BuiltinString t) = show t
instance Haskell.Eq BuiltinString where
  (==) (BuiltinString t) (BuiltinString t') = (==) t t'
instance Haskell.Ord BuiltinString where
  compare (BuiltinString t) (BuiltinString t') = compare t t'

-- | Appends a string to another and never fails.
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString (BuiltinString s1) (BuiltinString s2) = BuiltinString (s1 <> s2)
{-# OPAQUE appendString #-}

-- | An empty string.
emptyString :: BuiltinString
emptyString = BuiltinString Text.empty
{-# OPAQUE emptyString #-}

-- | Checks the equality of two strings and never fails.
equalsString :: BuiltinString -> BuiltinString -> Bool
equalsString (BuiltinString s1) (BuiltinString s2) = s1 == s2
{-# OPAQUE equalsString #-}

-- | Emits a trace message and never fails.
trace :: BuiltinString -> a -> a
trace _ x = x
{-# OPAQUE trace #-}

-- | Encodes a string into a bytestring and never fails.
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 (BuiltinString s) = BuiltinByteString $ Text.encodeUtf8 s
{-# OPAQUE encodeUtf8 #-}

{-
PAIR
-}

-- See Note [Opaque builtin types]
data BuiltinPair a b = BuiltinPair ~(a, b) deriving stock (Data)

instance (Haskell.Show a, Haskell.Show b) => Haskell.Show (BuiltinPair a b) where
  show (BuiltinPair p) = show p
instance (Haskell.Eq a, Haskell.Eq b) => Haskell.Eq (BuiltinPair a b) where
  (==) (BuiltinPair p) (BuiltinPair p') = (==) p p'
instance (Haskell.Ord a, Haskell.Ord b) => Haskell.Ord (BuiltinPair a b) where
  compare (BuiltinPair p) (BuiltinPair p') = compare p p'

-- | Takes first value from the tuple and never fails.
fst :: BuiltinPair a b -> a
fst (BuiltinPair (a, _)) = a
{-# OPAQUE fst #-}

-- | Takes second value from the tuple and never fails.
snd :: BuiltinPair a b -> b
snd (BuiltinPair (_, b)) = b
{-# OPAQUE snd #-}

-- | Constructs tuple from two builtin data.
mkPairData :: BuiltinData -> BuiltinData -> BuiltinPair BuiltinData BuiltinData
mkPairData d1 d2 = BuiltinPair (d1, d2)
{-# OPAQUE mkPairData #-}

{-
LIST
-}

-- See Note [Opaque builtin types]
data BuiltinList a = BuiltinList ~[a] deriving stock (Data)

instance Haskell.Show a => Haskell.Show (BuiltinList a) where
  show (BuiltinList l) = show l
instance Haskell.Eq a => Haskell.Eq (BuiltinList a) where
  (==) (BuiltinList l) (BuiltinList l') = (==) l l'
instance Haskell.Ord a => Haskell.Ord (BuiltinList a) where
  compare (BuiltinList l) (BuiltinList l') = compare l l'

-- | Checks if the given list is empty.
null :: BuiltinList a -> Bool
null (BuiltinList (_ : _)) = False
null (BuiltinList []) = True
{-# OPAQUE null #-}

-- | Takes the first element of the list and fails if given list is empty.
head :: BuiltinList a -> a
head (BuiltinList (x : _)) = x
head (BuiltinList []) = Haskell.error "empty list"
{-# OPAQUE head #-}

-- | Takes the last element of the list and fails if given list is empty.
tail :: BuiltinList a -> BuiltinList a
tail (BuiltinList (_ : xs)) = BuiltinList xs
tail (BuiltinList []) = Haskell.error "empty list"
{-# OPAQUE tail #-}

{-| Branches out depending on the structure of given list and never fails. If given list is empty,
  it will take the first branch and if not it will take the second branch. -}
chooseList :: BuiltinList a -> b -> b -> b
chooseList (BuiltinList []) b1 _ = b1
chooseList (BuiltinList (_ : _)) _ b2 = b2
{-# OPAQUE chooseList #-}

-- | Similar to 'chooseList' but deconstructs the list in case provided list is not empty.
caseList' :: forall a r. r -> (a -> BuiltinList a -> r) -> BuiltinList a -> r
caseList' nilCase _ (BuiltinList []) = nilCase
caseList' _ consCase (BuiltinList (x : xs)) = consCase x (BuiltinList xs)
{-# OPAQUE caseList' #-}

-- | Similar to caseList', but empty list case is omitted so passing empty list will raise error
unsafeCaseList :: forall a r. (a -> BuiltinList a -> r) -> BuiltinList a -> r
unsafeCaseList _ (BuiltinList []) = Haskell.error "empty list"
unsafeCaseList f (BuiltinList (x : xs)) = f x (BuiltinList xs)
{-# OPAQUE unsafeCaseList #-}

-- | Drops first n elements from the given list and never fails.
drop :: Integer -> BuiltinList a -> BuiltinList a
drop i (BuiltinList xs) = BuiltinList (Haskell.genericDrop i xs)
{-# OPAQUE drop #-}

{-| Creates an empty data list and never fails. Prefer using constant.
See Note [Constants vs built-in functions] -}
mkNilData :: BuiltinUnit -> BuiltinList BuiltinData
mkNilData _ = BuiltinList []
{-# OPAQUE mkNilData #-}

{-| Creates an empty data pair list and never fails. Prefer using constant.
See Note [Constants vs built-in functions] -}
mkNilPairData :: BuiltinUnit -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mkNilPairData _ = BuiltinList []
{-# OPAQUE mkNilPairData #-}

-- | Appends a new element to the given list and never fails.
mkCons :: a -> BuiltinList a -> BuiltinList a
mkCons a (BuiltinList as) = BuiltinList (a : as)
{-# OPAQUE mkCons #-}

{-
DATA
-}

{-|
A type corresponding to the Plutus Core builtin equivalent of 'PLC.Data'.

The point of this type is to be an opaque equivalent of 'PLC.Data', so as to
ensure that it is only used in ways that the compiler can handle.

As such, you should use this type in your on-chain code, and in any data structures
that you want to be representable on-chain.

For off-chain usage, there are conversion functions 'builtinDataToData' and
'dataToBuiltinData', but note that these will not work on-chain. -}
data BuiltinData = BuiltinData ~PLC.Data
  deriving stock (Data, Generic)

instance Haskell.Show BuiltinData where
  show (BuiltinData d) = show d
instance Haskell.Eq BuiltinData where
  (==) (BuiltinData d) (BuiltinData d') = (==) d d'
instance Haskell.Ord BuiltinData where
  compare (BuiltinData d) (BuiltinData d') = compare d d'
instance NFData BuiltinData where
  rnf (BuiltinData d) = rnf d
instance Pretty BuiltinData where
  pretty (BuiltinData d) = pretty d

-- NOT a builtin, only safe off-chain, hence the OPAQUE

-- | NOT a builtin. Converts a 'BuiltinData' into a 'PLC.Data'. Only works off-chain.
builtinDataToData :: BuiltinData -> PLC.Data
builtinDataToData (BuiltinData d) = d
{-# OPAQUE builtinDataToData #-}

-- NOT a builtin, only safe off-chain, hence the OPAQUE

-- | NOT a builtin. Converts a 'PLC.Data' into a 'BuiltinData'. Only works off-chain.
dataToBuiltinData :: PLC.Data -> BuiltinData
dataToBuiltinData = BuiltinData
{-# OPAQUE dataToBuiltinData #-}

-- | Branches out depending on the structure of given data and never fails.
chooseData :: forall a. BuiltinData -> a -> a -> a -> a -> a -> a
chooseData (BuiltinData d) constrCase mapCase listCase iCase bCase = case d of
  PLC.Constr {} -> constrCase
  PLC.Map {} -> mapCase
  PLC.List {} -> listCase
  PLC.I {} -> iCase
  PLC.B {} -> bCase
{-# OPAQUE chooseData #-}

-- | Creates 'Constr' data value with the given index and elements; never fails.
mkConstr :: BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData
mkConstr i (BuiltinList args) = BuiltinData (PLC.Constr i (fmap builtinDataToData args))
{-# OPAQUE mkConstr #-}

-- | Creates 'Map' data value with the given list of pairs and never fails.
mkMap :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData
mkMap (BuiltinList es) = BuiltinData (PLC.Map (fmap p2p es))
  where
    p2p (BuiltinPair (d, d')) = (builtinDataToData d, builtinDataToData d')
{-# OPAQUE mkMap #-}

-- | Creates 'List' data value with the given list and never fails.
mkList :: BuiltinList BuiltinData -> BuiltinData
mkList (BuiltinList l) = BuiltinData (PLC.List (fmap builtinDataToData l))
{-# OPAQUE mkList #-}

-- | Creates 'I' data value with the given integer and never fails.
mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)
{-# OPAQUE mkI #-}

-- | Creates 'B' data value with the given bytestring and never fails.
mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)
{-# OPAQUE mkB #-}

-- | Deconstructs the given data as a 'Constr', failing if it is not a 'Constr'.
unsafeDataAsConstr :: BuiltinData -> BuiltinPair BuiltinInteger (BuiltinList BuiltinData)
unsafeDataAsConstr (BuiltinData (PLC.Constr i args)) = BuiltinPair (i, BuiltinList $ fmap dataToBuiltinData args)
unsafeDataAsConstr _ = Haskell.error "not a Constr"
{-# OPAQUE unsafeDataAsConstr #-}

-- | Deconstructs the given data as a 'Map', failing if it is not a 'Map'.
unsafeDataAsMap :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
unsafeDataAsMap (BuiltinData (PLC.Map m)) = BuiltinList (fmap p2p m)
  where
    p2p (d, d') = BuiltinPair (dataToBuiltinData d, dataToBuiltinData d')
unsafeDataAsMap _ = Haskell.error "not a Map"
{-# OPAQUE unsafeDataAsMap #-}

-- | Deconstructs the given data as a 'List', failing if it is not a 'List'.
unsafeDataAsList :: BuiltinData -> BuiltinList BuiltinData
unsafeDataAsList (BuiltinData (PLC.List l)) = BuiltinList (fmap dataToBuiltinData l)
unsafeDataAsList _ = Haskell.error "not a List"
{-# OPAQUE unsafeDataAsList #-}

-- | Deconstructs the given data as a 'I', failing if it is not a 'I'.
unsafeDataAsI :: BuiltinData -> BuiltinInteger
unsafeDataAsI (BuiltinData (PLC.I i)) = i
unsafeDataAsI _ = Haskell.error "not an I"
{-# OPAQUE unsafeDataAsI #-}

-- | Deconstructs the given data as a 'B', failing if it is not a 'B'.
unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB (BuiltinData (PLC.B b)) = BuiltinByteString b
unsafeDataAsB _ = Haskell.error "not a B"
{-# OPAQUE unsafeDataAsB #-}

-- | Checks equality of two data and never fails.
equalsData :: BuiltinData -> BuiltinData -> Bool
equalsData (BuiltinData b1) (BuiltinData b2) = b1 Haskell.== b2
{-# OPAQUE equalsData #-}

{-| Serialize the given data into CBOR bytestring. See 'PlutusCore.Data' for exact encoder as 'Data'
does not uses Generic version. -}
serialiseData :: BuiltinData -> BuiltinByteString
serialiseData (BuiltinData b) = BuiltinByteString $ BSL.toStrict $ serialise b
{-# OPAQUE serialiseData #-}

{-
Value
-}

data BuiltinValue = BuiltinValue ~PLC.Value
  deriving stock (Generic)

{-
ARRAY
-}

data BuiltinArray a = BuiltinArray ~(Vector a) deriving stock (Data)

instance Haskell.Show a => Haskell.Show (BuiltinArray a) where
  show (BuiltinArray v) = show v
instance Haskell.Eq a => Haskell.Eq (BuiltinArray a) where
  (==) (BuiltinArray v1) (BuiltinArray v2) = (==) v1 v2
instance Haskell.Ord a => Haskell.Ord (BuiltinArray a) where
  compare (BuiltinArray v1) (BuiltinArray v2) = compare v1 v2

-- | Returns the length of the provided array and never fails
lengthOfArray :: BuiltinArray a -> BuiltinInteger
lengthOfArray (BuiltinArray v) = toInteger (Vector.length v)
{-# OPAQUE lengthOfArray #-}

-- | Converts given list into array and never fails.
listToArray :: BuiltinList a -> BuiltinArray a
listToArray (BuiltinList l) = BuiltinArray (Vector.fromList l)
{-# OPAQUE listToArray #-}

{-| Returns the n-th element from the array. Fails if the given index is not in the range @[0..j)@,
  where @j@ is the length of the array. -}
indexArray :: BuiltinArray a -> BuiltinInteger -> a
indexArray (BuiltinArray v) i = v Vector.! fromInteger i
{-# OPAQUE indexArray #-}

{-
BLS12_381
-}

{- Note [Wrapping the BLS12-381 types in PlutusTx]

As explained in Note [Wrapping the BLS12-381 types in Plutus Core], the types
exported by the Haskell bindings for the `blst` library are ForeignPtrs which
have to be wrapped in newtypes to keep the PLC builtin machinery happy.
However, there's a further complication in PlutusTx: if you try to use the
newtypes directly then the plugin sees through the newtypes to the foreign
pointers and fails because it doesn't know how to handle them.  To avoid this we
further wrap the newtypes in datatypes here.  We could have done this in Plutus
Core by using `data` instead of `newtype`, but then the code here dealing with
BLS types and builtins doesn't look like the code for the other builtins.
Because of this it seemed safer and more uniform to add the datatype wrapper
here rather than in the Plutus Core code.
-}

---------------- G1 ----------------

data BuiltinBLS12_381_G1_Element = BuiltinBLS12_381_G1_Element ~BLS12_381.G1.Element

instance Haskell.Show BuiltinBLS12_381_G1_Element where
  show (BuiltinBLS12_381_G1_Element a) = show a
instance Haskell.Eq BuiltinBLS12_381_G1_Element where
  (==) (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G1_Element b) = (==) a b
instance NFData BuiltinBLS12_381_G1_Element where
  rnf (BuiltinBLS12_381_G1_Element d) = rnf d
instance Pretty BuiltinBLS12_381_G1_Element where
  pretty (BuiltinBLS12_381_G1_Element a) = pretty a

-- | Checks equality of two G1 elements and never fails.
bls12_381_G1_equals :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> Bool
bls12_381_G1_equals a b = coerce ((==) @BuiltinBLS12_381_G1_Element) a b
{-# OPAQUE bls12_381_G1_equals #-}

-- | Adds two G1 elements and never fails.
bls12_381_G1_add
  :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_add (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G1_Element b) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.add a b)
{-# OPAQUE bls12_381_G1_add #-}

-- | Negates a G1 element and never fails.
bls12_381_G1_neg :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_neg (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.neg a)
{-# OPAQUE bls12_381_G1_neg #-}

-- | Multiplies a G1 element by a scalar and never fails.
bls12_381_G1_scalarMul
  :: BuiltinInteger -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_scalarMul n (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.scalarMul n a)
{-# OPAQUE bls12_381_G1_scalarMul #-}

bls12_381_G1_multiScalarMul :: BuiltinList BuiltinInteger -> BuiltinList BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_multiScalarMul (BuiltinList ns) (BuiltinList ps) =
  case BLS12_381.G1.multiScalarMul ns (fmap (\(BuiltinBLS12_381_G1_Element p) -> p) ps) of
    BuiltinSuccess p -> BuiltinBLS12_381_G1_Element p
    BuiltinSuccessWithLogs logs p -> traceAll logs (BuiltinBLS12_381_G1_Element p)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $ Haskell.error "bls12_381_G1_multiScalarMul failed."

-- | Compresses a G1 element to a bytestring and never fails.
bls12_381_G1_compress :: BuiltinBLS12_381_G1_Element -> BuiltinByteString
bls12_381_G1_compress (BuiltinBLS12_381_G1_Element a) = BuiltinByteString (BLS12_381.G1.compress a)
{-# OPAQUE bls12_381_G1_compress #-}

-- | Uncompresses a bytestring to a G1 element, failing if the bytestring is not a valid compressed G1 element.
bls12_381_G1_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_uncompress (BuiltinByteString b) =
  case BLS12_381.G1.uncompress b of
    Left err -> Haskell.error $ "BSL12_381 G1 uncompression error: " ++ show err
    Right a -> BuiltinBLS12_381_G1_Element a
{-# OPAQUE bls12_381_G1_uncompress #-}

{-| Hashes an arbitrary bytestring message to a G1 element using the given domain separation tag (DST),
failing if length of the DST is bigger than 255 bytes. -}
bls12_381_G1_hashToGroup :: BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
  case BLS12_381.G1.hashToGroup msg dst of
    Left err -> Haskell.error $ show err
    Right p -> BuiltinBLS12_381_G1_Element p
{-# OPAQUE bls12_381_G1_hashToGroup #-}

-- | The compressed form of the G1 identity element.
bls12_381_G1_compressed_zero :: BuiltinByteString
bls12_381_G1_compressed_zero = BuiltinByteString BLS12_381.G1.compressed_zero
{-# OPAQUE bls12_381_G1_compressed_zero #-}

-- | The compressed form of the G1 generator element.
bls12_381_G1_compressed_generator :: BuiltinByteString
bls12_381_G1_compressed_generator = BuiltinByteString BLS12_381.G1.compressed_generator
{-# OPAQUE bls12_381_G1_compressed_generator #-}

---------------- G2 ----------------

data BuiltinBLS12_381_G2_Element = BuiltinBLS12_381_G2_Element ~BLS12_381.G2.Element

instance Haskell.Show BuiltinBLS12_381_G2_Element where
  show (BuiltinBLS12_381_G2_Element a) = show a
instance Haskell.Eq BuiltinBLS12_381_G2_Element where
  (==) (BuiltinBLS12_381_G2_Element a) (BuiltinBLS12_381_G2_Element b) = (==) a b
instance NFData BuiltinBLS12_381_G2_Element where
  rnf (BuiltinBLS12_381_G2_Element d) = rnf d
instance Pretty BuiltinBLS12_381_G2_Element where
  pretty (BuiltinBLS12_381_G2_Element a) = pretty a

-- | Checks equality of two G2 elements and never fails.
bls12_381_G2_equals :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> Bool
bls12_381_G2_equals a b = coerce ((==) @BuiltinBLS12_381_G2_Element) a b
{-# OPAQUE bls12_381_G2_equals #-}

-- | Adds two G2 elements and never fails.
bls12_381_G2_add
  :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_add (BuiltinBLS12_381_G2_Element a) (BuiltinBLS12_381_G2_Element b) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.add a b)
{-# OPAQUE bls12_381_G2_add #-}

-- | Negates a G2 element and never fails.
bls12_381_G2_neg :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_neg (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.neg a)
{-# OPAQUE bls12_381_G2_neg #-}

-- | Multiplies a G2 element by a scalar and never fails.
bls12_381_G2_scalarMul
  :: BuiltinInteger -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_scalarMul n (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.scalarMul n a)
{-# OPAQUE bls12_381_G2_scalarMul #-}

bls12_381_G2_multiScalarMul :: BuiltinList BuiltinInteger -> BuiltinList BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_multiScalarMul (BuiltinList ns) (BuiltinList ps) =
  case BLS12_381.G2.multiScalarMul ns (fmap (\(BuiltinBLS12_381_G2_Element p) -> p) ps) of
    BuiltinSuccess p -> BuiltinBLS12_381_G2_Element p
    BuiltinSuccessWithLogs logs p -> traceAll logs (BuiltinBLS12_381_G2_Element p)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $ Haskell.error "bls12_381_G2_multiScalarMul failed."
{-# OPAQUE bls12_381_G2_multiScalarMul #-}

-- | Compresses a G2 element to a bytestring and never fails.
bls12_381_G2_compress :: BuiltinBLS12_381_G2_Element -> BuiltinByteString
bls12_381_G2_compress (BuiltinBLS12_381_G2_Element a) = BuiltinByteString (BLS12_381.G2.compress a)
{-# OPAQUE bls12_381_G2_compress #-}

-- | Uncompresses a bytestring to a G2 element, failing if the bytestring is not a valid compressed G2 element.
bls12_381_G2_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_uncompress (BuiltinByteString b) =
  case BLS12_381.G2.uncompress b of
    Left err -> Haskell.error $ "BSL12_381 G2 uncompression error: " ++ show err
    Right a -> BuiltinBLS12_381_G2_Element a
{-# OPAQUE bls12_381_G2_uncompress #-}

{-| Hashes an arbitrary bytestring message to a G2 element using the given domain separation tag (DST),
failing if length of the DST is bigger than 255 bytes. -}
bls12_381_G2_hashToGroup :: BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
  case BLS12_381.G2.hashToGroup msg dst of
    Left err -> Haskell.error $ show err
    Right p -> BuiltinBLS12_381_G2_Element p
{-# OPAQUE bls12_381_G2_hashToGroup #-}

-- | The compressed form of the G2 identity element (also known as zero or point at infinity).
bls12_381_G2_compressed_zero :: BuiltinByteString
bls12_381_G2_compressed_zero = BuiltinByteString BLS12_381.G2.compressed_zero
{-# OPAQUE bls12_381_G2_compressed_zero #-}

-- | The compressed form of the G2 generator element.
bls12_381_G2_compressed_generator :: BuiltinByteString
bls12_381_G2_compressed_generator = BuiltinByteString BLS12_381.G2.compressed_generator
{-# OPAQUE bls12_381_G2_compressed_generator #-}

---------------- Pairing ----------------

data BuiltinBLS12_381_MlResult = BuiltinBLS12_381_MlResult ~BLS12_381.Pairing.MlResult

instance Haskell.Show BuiltinBLS12_381_MlResult where
  show (BuiltinBLS12_381_MlResult a) = show a
instance Haskell.Eq BuiltinBLS12_381_MlResult where
  (==) (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b) = (==) a b
instance NFData BuiltinBLS12_381_MlResult where
  rnf (BuiltinBLS12_381_MlResult a) = rnf a
instance Pretty BuiltinBLS12_381_MlResult where
  pretty (BuiltinBLS12_381_MlResult a) = pretty a

-- | Computes the Miller loop between a G1 element and a G2 element and never fails.
bls12_381_millerLoop
  :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_MlResult
bls12_381_millerLoop (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G2_Element b) =
  BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.millerLoop a b
{-# OPAQUE bls12_381_millerLoop #-}

-- | Multiplies two Miller loop results and never fails.
bls12_381_mulMlResult
  :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult
bls12_381_mulMlResult (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b) =
  BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.mulMlResult a b
{-# OPAQUE bls12_381_mulMlResult #-}

{-| Performs the final verification step of a pairing check. Returns true if e(P,Q) == e(R,S) for
the given Miller loop results, and never fails. -}
bls12_381_finalVerify :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> Bool
bls12_381_finalVerify (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b) =
  BLS12_381.Pairing.finalVerify a b
{-# OPAQUE bls12_381_finalVerify #-}

{-
CONVERSION
-}

{-| Converts the given integer to a bytestring. The first argument specifies
 endianness (True for big-endian), followed by the target length of the resulting bytestring
 and the integer itself. Fails if the target length is greater than 8192 or if the length
 argument is 0 and the result won't fit into 8192 bytes.
 See 'PlutusCore.Bitwise.integerToByteString' for its invariants in detail. -}
integerToByteString
  :: Bool
  -> BuiltinInteger
  -> BuiltinInteger
  -> BuiltinByteString
integerToByteString endiannessArg paddingArg input =
  case Bitwise.integerToByteString endiannessArg paddingArg input of
    BuiltinSuccess bs -> BuiltinByteString bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ BuiltinByteString bs
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "Integer to ByteString conversion errored."
{-# OPAQUE integerToByteString #-}

{-| Converts the given bytestring to the integer and never fails. The first argument specifies
endianness (True for big-endian), followed by the bytestring. -}
byteStringToInteger
  :: Bool
  -> BuiltinByteString
  -> BuiltinInteger
byteStringToInteger statedEndianness (BuiltinByteString input) =
  Bitwise.byteStringToInteger statedEndianness input
{-# OPAQUE byteStringToInteger #-}

{-
BITWISE
-}

{-| Shifts the bytestring to the left if the second argument is positive, and to the right otherwise.
Right-shifts fill with 0s from the left (logical shift); left-shifts fill with 0s from the right.
Never fails. -}
shiftByteString
  :: BuiltinByteString
  -> BuiltinInteger
  -> BuiltinByteString
shiftByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.shiftByteString bs
{-# OPAQUE shiftByteString #-}

{-| Rotates the bytestring to the left if the second argument is positive, and to the right otherwise.
Never fails. -}
rotateByteString
  :: BuiltinByteString
  -> BuiltinInteger
  -> BuiltinByteString
rotateByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.rotateByteString bs
{-# OPAQUE rotateByteString #-}

-- | Counts the number of bits set to 1 in the bytestring and never fails.
countSetBits
  :: BuiltinByteString
  -> BuiltinInteger
countSetBits (BuiltinByteString bs) = fromIntegral . Bitwise.countSetBits $ bs
{-# OPAQUE countSetBits #-}

{-| Finds the index of the first bit set to 1 in the bytestring. If the bytestring consists only of
0s, it returns the length of the bytestring in bits. Never fails. -}
findFirstSetBit
  :: BuiltinByteString
  -> BuiltinInteger
findFirstSetBit (BuiltinByteString bs) =
  fromIntegral . Bitwise.findFirstSetBit $ bs
{-# OPAQUE findFirstSetBit #-}

{-
LOGICAL
-}

{-| Performs a bitwise AND on two bytestrings. The first boolean argument indicates whether to use
padding (True) or truncation (False) if the bytestrings have different lengths. Never fails. -}
andByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
andByteString isPaddingSemantics (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.andByteString isPaddingSemantics data1 $ data2
{-# OPAQUE andByteString #-}

{-| Performs a bitwise OR on two bytestrings. The first boolean argument indicates whether to use
padding (True) or truncation (False) if the bytestrings have different lengths. Never fails. -}
orByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
orByteString isPaddingSemantics (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.orByteString isPaddingSemantics data1 $ data2
{-# OPAQUE orByteString #-}

{-| Performs a bitwise XOR on two bytestrings. The first boolean argument indicates whether to use
padding (True) or truncation (False) if the bytestrings have different lengths. Never fails. -}
xorByteString
  :: Bool
  -> BuiltinByteString
  -> BuiltinByteString
  -> BuiltinByteString
xorByteString isPaddingSemantics (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.xorByteString isPaddingSemantics data1 $ data2
{-# OPAQUE xorByteString #-}

-- | Performs a bitwise complement on the bytestring and never fails.
complementByteString
  :: BuiltinByteString
  -> BuiltinByteString
complementByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.complementByteString $ bs
{-# OPAQUE complementByteString #-}

-- | Reads the bit at the given index in the bytestring. Fails if the index is out of bounds.
readBit
  :: BuiltinByteString
  -> BuiltinInteger
  -> Bool
readBit (BuiltinByteString bs) i =
  case Bitwise.readBit bs (fromIntegral i) of
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "readBit errored."
    BuiltinSuccess b -> b
    BuiltinSuccessWithLogs logs b -> traceAll logs b
{-# OPAQUE readBit #-}

{-| Writes the given bit (third argument, True for 1, False for 0) at the specified indices (second argument) in the bytestring.
Fails if any index is out of bounds. -}
writeBits
  :: BuiltinByteString
  -> BuiltinList BuiltinInteger
  -> Bool
  -> BuiltinByteString
writeBits (BuiltinByteString bs) (BuiltinList ixes) bit =
  case Bitwise.writeBits bs ixes bit of
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "writeBits errored."
    BuiltinSuccess bs' -> BuiltinByteString bs'
    BuiltinSuccessWithLogs logs bs' -> traceAll logs $ BuiltinByteString bs'
{-# OPAQUE writeBits #-}

{-| Creates a bytestring of a given length by repeating the given byte.
Fails if the byte, second argument, is not in range @[0,255]@, the length is negative,
or when the length is greater than 8192. -}
replicateByte
  :: BuiltinInteger
  -> BuiltinInteger
  -> BuiltinByteString
replicateByte n w8 =
  case Bitwise.replicateByte n (fromIntegral w8) of
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "byteStringReplicate errored."
    BuiltinSuccess bs -> BuiltinByteString bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ BuiltinByteString bs
{-# OPAQUE replicateByte #-}

{-| Computes modular exponentiation (base^exponent mod modulus). Fails if the modulus is zero or negative,
or if the exponent is negative and the modular inverse does not exist. -}
expModInteger
  :: BuiltinInteger
  -> BuiltinInteger
  -> BuiltinInteger
  -> BuiltinInteger
expModInteger b e m =
  -- (fromInteger @Natural) correctly throws an underflow exception upon negative integer
  case ExpMod.expMod b e (fromInteger m) of
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "expModInteger errored."
    BuiltinSuccess bs -> toInteger bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ toInteger bs
{-# OPAQUE expModInteger #-}

insertCoin
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinInteger
  -> BuiltinValue
  -> BuiltinValue
insertCoin (BuiltinByteString c) (BuiltinByteString t) amt (BuiltinValue v0) =
  case Value.insertCoin c t amt v0 of
    BuiltinSuccess v -> BuiltinValue v
    BuiltinSuccessWithLogs logs v -> traceAll logs (BuiltinValue v)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "insertCoin errored."
{-# OPAQUE insertCoin #-}

lookupCoin
  :: BuiltinByteString
  -> BuiltinByteString
  -> BuiltinValue
  -> Integer
lookupCoin (BuiltinByteString c) (BuiltinByteString t) (BuiltinValue v) =
  Value.lookupCoin c t v
{-# OPAQUE lookupCoin #-}

unionValue :: BuiltinValue -> BuiltinValue -> BuiltinValue
unionValue (BuiltinValue v1) (BuiltinValue v2) =
  case Value.unionValue v1 v2 of
    BuiltinSuccess v -> BuiltinValue v
    BuiltinSuccessWithLogs logs v -> traceAll logs (BuiltinValue v)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $ Haskell.error "unionValue errored."
{-# OPAQUE unionValue #-}

valueContains :: BuiltinValue -> BuiltinValue -> Bool
valueContains (BuiltinValue v1) (BuiltinValue v2) =
  case Value.valueContains v1 v2 of
    BuiltinSuccess r -> r
    BuiltinSuccessWithLogs logs r -> traceAll logs r
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "valueContains errored."
{-# OPAQUE valueContains #-}

mkValue :: BuiltinValue -> BuiltinData
mkValue (BuiltinValue v) = BuiltinData $ Value.valueData v
{-# OPAQUE mkValue #-}

unsafeDataAsValue :: BuiltinData -> BuiltinValue
unsafeDataAsValue (BuiltinData d) =
  case Value.unValueData d of
    BuiltinSuccess v -> BuiltinValue v
    BuiltinSuccessWithLogs logs v -> traceAll logs (BuiltinValue v)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "Data to Value conversion errored."
{-# OPAQUE unsafeDataAsValue #-}

scaleValue :: Integer -> BuiltinValue -> BuiltinValue
scaleValue c (BuiltinValue val) =
  case Value.scaleValue c val of
    BuiltinSuccess v -> BuiltinValue v
    BuiltinSuccessWithLogs logs v -> traceAll logs (BuiltinValue v)
    BuiltinFailure logs err ->
      traceAll (logs <> pure (display err)) $
        Haskell.error "scaleValue errored."
{-# OPAQUE scaleValue #-}

caseInteger :: Integer -> [a] -> a
caseInteger i b = b !! fromIntegral i
{-# OPAQUE caseInteger #-}

{-| Case matching on a builtin pair. Continuation is needed here to make
it more efficient on builtin-casing implementation. -}
casePair :: forall a b r. BuiltinPair a b -> (a -> b -> r) -> r
casePair p f = f (PlutusTx.Builtins.Internal.fst p) (PlutusTx.Builtins.Internal.snd p)
{-# INLINE casePair #-}
