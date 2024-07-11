-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

-- This ensures that we don't put *anything* about these functions into the interface
-- file, otherwise GHC can be clever about the ones that are always error, even though
-- they're NOINLINE!
{-# OPTIONS_GHC -O0 #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-} -- See Note [Opaque builtin types]

-- | This module contains the special Haskell names that are used to map to builtin types or functions
-- in Plutus Core.
--
-- Most users should not use this module directly, but rather use 'PlutusTx.Builtins'.
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
import Data.Text as Text (Text, empty)
import Data.Text.Encoding as Text (decodeUtf8, encodeUtf8)
import GHC.Generics (Generic)
import PlutusCore.Bitwise qualified as Bitwise
import PlutusCore.Builtin (BuiltinResult (..))
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Crypto.Ed25519 qualified
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusCore.Crypto.Secp256k1 qualified
import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty (Pretty (..), display)
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

{-# NOINLINE error #-}
error :: BuiltinUnit -> a
error = Haskell.error "PlutusTx.Builtins.Internal.error"

{-
BOOL
-}

-- See Note [Opaque builtin types]
data BuiltinBool = BuiltinBool ~Bool deriving stock Data

{-# NOINLINE true #-}
true :: BuiltinBool
true = BuiltinBool True

{-# NOINLINE false #-}
false :: BuiltinBool
false = BuiltinBool False

{-# NOINLINE ifThenElse #-}
ifThenElse :: BuiltinBool -> a -> a -> a
ifThenElse (BuiltinBool b) x y = if b then x else y

{-
UNIT
-}

-- See Note [Opaque builtin types]
data BuiltinUnit = BuiltinUnit ~() deriving stock Data

{-# NOINLINE unitval #-}
unitval :: BuiltinUnit
unitval = BuiltinUnit ()

{-# NOINLINE chooseUnit #-}
chooseUnit :: BuiltinUnit -> a -> a
chooseUnit (BuiltinUnit ()) a = a

{-
INTEGER
-}

-- I'm somewhat surprised that this works despite not being opaque! GHC doesn't seem to
-- mess with 'Integer', which is suspicious to me. Probably we *should* make 'BuiltinInteger'
-- opaque, but that's going to really mess with our users' code...
type BuiltinInteger = Integer

{-# NOINLINE addInteger #-}
addInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
addInteger = coerce ((+) @Integer)

{-# NOINLINE subtractInteger #-}
subtractInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
subtractInteger = coerce ((-) @Integer)

{-# NOINLINE multiplyInteger #-}
multiplyInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
multiplyInteger = coerce ((*) @Integer)

{-# NOINLINE divideInteger #-}
divideInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
divideInteger = coerce (div @Integer)

{-# NOINLINE modInteger #-}
modInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
modInteger = coerce (mod @Integer)

{-# NOINLINE quotientInteger #-}
quotientInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
quotientInteger = coerce (quot @Integer)

{-# NOINLINE remainderInteger #-}
remainderInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
remainderInteger = coerce (rem @Integer)

{-# NOINLINE lessThanInteger #-}
lessThanInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanInteger x y = BuiltinBool $ coerce ((<) @Integer) x  y

{-# NOINLINE lessThanEqualsInteger #-}
lessThanEqualsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanEqualsInteger x y = BuiltinBool $ coerce ((<=) @Integer) x y

{-# NOINLINE equalsInteger #-}
equalsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
equalsInteger x y = BuiltinBool $ coerce ((==) @Integer) x y

{-
BYTESTRING
-}

-- See Note [Opaque builtin types]
-- | An opaque type representing Plutus Core ByteStrings.
data BuiltinByteString = BuiltinByteString ~BS.ByteString deriving stock Data

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
    hashWithSalt s (BuiltinByteString bs )= hashWithSalt s bs
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

{-# NOINLINE appendByteString #-}
appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinByteString $ BS.append b1 b2

{-# NOINLINE consByteString #-}
consByteString :: BuiltinInteger -> BuiltinByteString -> BuiltinByteString
consByteString n (BuiltinByteString b) = BuiltinByteString $ BS.cons (fromIntegral n) b

{-# NOINLINE sliceByteString #-}
sliceByteString :: BuiltinInteger -> BuiltinInteger -> BuiltinByteString -> BuiltinByteString
sliceByteString start n (BuiltinByteString b) = BuiltinByteString $ BS.take (fromIntegral n) (BS.drop (fromIntegral start) b)

{-# NOINLINE lengthOfByteString #-}
lengthOfByteString :: BuiltinByteString -> BuiltinInteger
lengthOfByteString (BuiltinByteString b) = toInteger $ BS.length b

{-# NOINLINE indexByteString #-}
indexByteString :: BuiltinByteString -> BuiltinInteger -> BuiltinInteger
indexByteString (BuiltinByteString b) i = toInteger $ BS.index b (fromInteger i)

{-# NOINLINE emptyByteString #-}
emptyByteString :: BuiltinByteString
emptyByteString = BuiltinByteString BS.empty

{-# NOINLINE sha2_256 #-}
sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha2_256 b

{-# NOINLINE sha3_256 #-}
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha3_256 b

{-# NOINLINE blake2b_224 #-}
blake2b_224 :: BuiltinByteString -> BuiltinByteString
blake2b_224 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_224 b

{-# NOINLINE blake2b_256 #-}
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_256 b

{-# NOINLINE keccak_256 #-}
keccak_256 :: BuiltinByteString -> BuiltinByteString
keccak_256 (BuiltinByteString b) = BuiltinByteString $ Hash.keccak_256 b

{-# NOINLINE verifyEd25519Signature #-}
verifyEd25519Signature :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> BuiltinBool
verifyEd25519Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Ed25519.verifyEd25519Signature_V1 vk msg sig of
    BuiltinSuccess b              -> BuiltinBool b
    BuiltinSuccessWithLogs logs b -> traceAll logs $ BuiltinBool b
    BuiltinFailure logs err       -> traceAll (logs <> pure (display err)) $
        Haskell.error "Ed25519 signature verification errored."

{-# NOINLINE verifyEcdsaSecp256k1Signature #-}
verifyEcdsaSecp256k1Signature ::
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinBool
verifyEcdsaSecp256k1Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Secp256k1.verifyEcdsaSecp256k1Signature vk msg sig of
    BuiltinSuccess b              -> BuiltinBool b
    BuiltinSuccessWithLogs logs b -> traceAll logs $ BuiltinBool b
    BuiltinFailure logs err       -> traceAll (logs <> pure (display err)) $
        Haskell.error "ECDSA SECP256k1 signature verification errored."

{-# NOINLINE verifySchnorrSecp256k1Signature #-}
verifySchnorrSecp256k1Signature ::
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinBool
verifySchnorrSecp256k1Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Secp256k1.verifySchnorrSecp256k1Signature vk msg sig of
    BuiltinSuccess b              -> BuiltinBool b
    BuiltinSuccessWithLogs logs b -> traceAll logs $ BuiltinBool b
    BuiltinFailure logs err       -> traceAll (logs <> pure (display err)) $
        Haskell.error "Schnorr SECP256k1 signature verification errored."

traceAll :: forall (a :: Type) (f :: Type -> Type) .
  (Foldable f) => f Text -> a -> a
traceAll logs x = Foldable.foldl' (\acc t -> trace (BuiltinString t) acc) x logs

{-# NOINLINE equalsByteString #-}
equalsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
equalsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 == b2

{-# NOINLINE lessThanByteString #-}
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 < b2

{-# NOINLINE lessThanEqualsByteString #-}
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanEqualsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 <= b2

{-# NOINLINE decodeUtf8 #-}
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 (BuiltinByteString b) = BuiltinString $ Text.decodeUtf8 b

{-
STRING
-}

-- See Note [Opaque builtin types]
data BuiltinString = BuiltinString ~Text deriving stock Data

instance Haskell.Show BuiltinString where
    show (BuiltinString t) = show t
instance Haskell.Eq BuiltinString where
    (==) (BuiltinString t) (BuiltinString t') = (==) t t'
instance Haskell.Ord BuiltinString where
    compare (BuiltinString t) (BuiltinString t') = compare t t'

{-# NOINLINE appendString #-}
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString (BuiltinString s1) (BuiltinString s2) = BuiltinString (s1 <> s2)

{-# NOINLINE emptyString #-}
emptyString :: BuiltinString
emptyString = BuiltinString Text.empty

{-# NOINLINE equalsString #-}
equalsString :: BuiltinString -> BuiltinString -> BuiltinBool
equalsString (BuiltinString s1) (BuiltinString s2) = BuiltinBool $ s1 == s2

{-# NOINLINE trace #-}
trace :: BuiltinString -> a -> a
trace _ x = x

{-# NOINLINE encodeUtf8 #-}
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 (BuiltinString s) = BuiltinByteString $ Text.encodeUtf8 s

{-
PAIR
-}

-- See Note [Opaque builtin types]
data BuiltinPair a b = BuiltinPair ~(a, b) deriving stock Data

instance (Haskell.Show a, Haskell.Show b) => Haskell.Show (BuiltinPair a b) where
    show (BuiltinPair p) = show p
instance (Haskell.Eq a, Haskell.Eq b) => Haskell.Eq (BuiltinPair a b) where
    (==) (BuiltinPair p) (BuiltinPair p') = (==) p p'
instance (Haskell.Ord a, Haskell.Ord b) => Haskell.Ord (BuiltinPair a b) where
    compare (BuiltinPair p) (BuiltinPair p') = compare p p'

{-# NOINLINE fst #-}
fst :: BuiltinPair a b -> a
fst (BuiltinPair (a, _)) = a

{-# NOINLINE snd #-}
snd :: BuiltinPair a b -> b
snd (BuiltinPair (_, b)) = b

{-# NOINLINE mkPairData #-}
mkPairData :: BuiltinData -> BuiltinData -> BuiltinPair BuiltinData BuiltinData
mkPairData d1 d2 = BuiltinPair (d1, d2)

{-
LIST
-}

-- See Note [Opaque builtin types]
data BuiltinList a = BuiltinList ~[a] deriving stock Data

instance Haskell.Show a => Haskell.Show (BuiltinList a) where
    show (BuiltinList l) = show l
instance Haskell.Eq a => Haskell.Eq (BuiltinList a) where
    (==) (BuiltinList l) (BuiltinList l') = (==) l l'
instance Haskell.Ord a => Haskell.Ord (BuiltinList a) where
    compare (BuiltinList l) (BuiltinList l') = compare l l'

{-# NOINLINE null #-}
null :: BuiltinList a -> BuiltinBool
null (BuiltinList (_:_)) = BuiltinBool False
null (BuiltinList [])    = BuiltinBool True

{-# NOINLINE head #-}
head :: BuiltinList a -> a
head (BuiltinList (x:_)) = x
head (BuiltinList [])    = Haskell.error "empty list"

{-# NOINLINE tail #-}
tail :: BuiltinList a -> BuiltinList a
tail (BuiltinList (_:xs)) = BuiltinList xs
tail (BuiltinList [])     = Haskell.error "empty list"

{-# NOINLINE chooseList #-}
chooseList :: BuiltinList a -> b -> b -> b
chooseList (BuiltinList [])    b1 _ = b1
chooseList (BuiltinList (_:_)) _ b2 = b2

{-# NOINLINE mkNilData #-}
mkNilData :: BuiltinUnit -> BuiltinList BuiltinData
mkNilData _ = BuiltinList []

{-# NOINLINE mkNilPairData #-}
mkNilPairData :: BuiltinUnit -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mkNilPairData _ = BuiltinList []

{-# NOINLINE mkCons #-}
mkCons :: a -> BuiltinList a -> BuiltinList a
mkCons a (BuiltinList as) = BuiltinList (a:as)

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
'dataToBuiltinData', but note that these will not work on-chain.
-}
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

-- NOT a builtin, only safe off-chain, hence the NOINLINE
{-# NOINLINE builtinDataToData #-}
-- | Convert a 'BuiltinData' into a 'PLC.Data'. Only works off-chain.
builtinDataToData :: BuiltinData -> PLC.Data
builtinDataToData (BuiltinData d) = d

-- NOT a builtin, only safe off-chain, hence the NOINLINE
{-# NOINLINE dataToBuiltinData #-}
-- | Convert a 'PLC.Data' into a 'BuiltinData'. Only works off-chain.
dataToBuiltinData :: PLC.Data -> BuiltinData
dataToBuiltinData = BuiltinData

{-# NOINLINE chooseData #-}
chooseData :: forall a . BuiltinData -> a -> a -> a -> a -> a -> a
chooseData (BuiltinData d) constrCase mapCase listCase iCase bCase = case d of
    PLC.Constr{} -> constrCase
    PLC.Map{}    -> mapCase
    PLC.List{}   -> listCase
    PLC.I{}      -> iCase
    PLC.B{}      -> bCase

{-# NOINLINE mkConstr #-}
mkConstr :: BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData
mkConstr i (BuiltinList args) = BuiltinData (PLC.Constr i (fmap builtinDataToData args))

{-# NOINLINE mkMap #-}
mkMap :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData
mkMap (BuiltinList es) = BuiltinData (PLC.Map (fmap p2p es))
  where
      p2p (BuiltinPair (d, d')) = (builtinDataToData d, builtinDataToData d')

{-# NOINLINE mkList #-}
mkList :: BuiltinList BuiltinData -> BuiltinData
mkList (BuiltinList l) = BuiltinData (PLC.List (fmap builtinDataToData l))

{-# NOINLINE mkI #-}
mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)

{-# NOINLINE mkB #-}
mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)

{-# NOINLINE unsafeDataAsConstr #-}
unsafeDataAsConstr :: BuiltinData -> BuiltinPair BuiltinInteger (BuiltinList BuiltinData)
unsafeDataAsConstr (BuiltinData (PLC.Constr i args)) = BuiltinPair (i, BuiltinList $ fmap dataToBuiltinData args)
unsafeDataAsConstr _                                 = Haskell.error "not a Constr"

{-# NOINLINE unsafeDataAsMap #-}
unsafeDataAsMap :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
unsafeDataAsMap (BuiltinData (PLC.Map m)) = BuiltinList (fmap p2p m)
  where
      p2p (d, d') = BuiltinPair (dataToBuiltinData d, dataToBuiltinData d')
unsafeDataAsMap _                         = Haskell.error "not a Map"

{-# NOINLINE unsafeDataAsList #-}
unsafeDataAsList :: BuiltinData -> BuiltinList BuiltinData
unsafeDataAsList (BuiltinData (PLC.List l)) = BuiltinList (fmap dataToBuiltinData l)
unsafeDataAsList _                          = Haskell.error "not a List"

{-# NOINLINE unsafeDataAsI #-}
unsafeDataAsI :: BuiltinData -> BuiltinInteger
unsafeDataAsI (BuiltinData (PLC.I i)) = i
unsafeDataAsI _                       = Haskell.error "not an I"

{-# NOINLINE unsafeDataAsB #-}
unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB (BuiltinData (PLC.B b)) = BuiltinByteString b
unsafeDataAsB _                       = Haskell.error "not a B"

{-# NOINLINE equalsData #-}
equalsData :: BuiltinData -> BuiltinData -> BuiltinBool
equalsData (BuiltinData b1) (BuiltinData b2) = BuiltinBool $ b1 Haskell.== b2

{-# NOINLINE serialiseData #-}
serialiseData :: BuiltinData -> BuiltinByteString
serialiseData (BuiltinData b) = BuiltinByteString $ BSL.toStrict $ serialise b


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

{-# NOINLINE bls12_381_G1_equals #-}
bls12_381_G1_equals :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBool
bls12_381_G1_equals a b = BuiltinBool $ coerce ((==) @BuiltinBLS12_381_G1_Element) a b

{-# NOINLINE bls12_381_G1_add #-}
bls12_381_G1_add :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_add (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G1_Element b) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.add a b)

{-# NOINLINE bls12_381_G1_neg #-}
bls12_381_G1_neg :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_neg (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.neg a)

{-# NOINLINE bls12_381_G1_scalarMul #-}
bls12_381_G1_scalarMul :: BuiltinInteger -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_scalarMul n (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.scalarMul n a)

{-# NOINLINE bls12_381_G1_compress #-}
bls12_381_G1_compress :: BuiltinBLS12_381_G1_Element -> BuiltinByteString
bls12_381_G1_compress (BuiltinBLS12_381_G1_Element a) = BuiltinByteString (BLS12_381.G1.compress a)

{-# NOINLINE bls12_381_G1_uncompress #-}
bls12_381_G1_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_uncompress (BuiltinByteString b) =
    case BLS12_381.G1.uncompress b of
      Left err -> Haskell.error $ "BSL12_381 G1 uncompression error: " ++ show err
      Right a  -> BuiltinBLS12_381_G1_Element a

{-# NOINLINE bls12_381_G1_hashToGroup #-}
bls12_381_G1_hashToGroup ::  BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
    case BLS12_381.G1.hashToGroup msg dst of
      Left err -> Haskell.error $ show err
      Right p  -> BuiltinBLS12_381_G1_Element p

{-# NOINLINE bls12_381_G1_compressed_zero #-}
bls12_381_G1_compressed_zero :: BuiltinByteString
bls12_381_G1_compressed_zero = BuiltinByteString BLS12_381.G1.compressed_zero

{-# NOINLINE bls12_381_G1_compressed_generator #-}
bls12_381_G1_compressed_generator :: BuiltinByteString
bls12_381_G1_compressed_generator = BuiltinByteString BLS12_381.G1.compressed_generator

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

{-# NOINLINE bls12_381_G2_equals #-}
bls12_381_G2_equals :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBool
bls12_381_G2_equals a b = BuiltinBool $ coerce ((==) @BuiltinBLS12_381_G2_Element) a b

{-# NOINLINE bls12_381_G2_add #-}
bls12_381_G2_add :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_add (BuiltinBLS12_381_G2_Element a) (BuiltinBLS12_381_G2_Element b) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.add a b)

{-# NOINLINE bls12_381_G2_neg #-}
bls12_381_G2_neg :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_neg (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.neg a)

{-# NOINLINE bls12_381_G2_scalarMul #-}
bls12_381_G2_scalarMul :: BuiltinInteger -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_scalarMul n (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.scalarMul n a)

{-# NOINLINE bls12_381_G2_compress #-}
bls12_381_G2_compress :: BuiltinBLS12_381_G2_Element -> BuiltinByteString
bls12_381_G2_compress (BuiltinBLS12_381_G2_Element a) = BuiltinByteString (BLS12_381.G2.compress a)

{-# NOINLINE bls12_381_G2_uncompress #-}
bls12_381_G2_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_uncompress (BuiltinByteString b) =
    case BLS12_381.G2.uncompress b of
      Left err -> Haskell.error $ "BSL12_381 G2 uncompression error: " ++ show err
      Right a  -> BuiltinBLS12_381_G2_Element a

{-# NOINLINE bls12_381_G2_hashToGroup #-}
bls12_381_G2_hashToGroup ::  BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
    case BLS12_381.G2.hashToGroup msg dst of
      Left err -> Haskell.error $ show err
      Right p  -> BuiltinBLS12_381_G2_Element p

{-# NOINLINE bls12_381_G2_compressed_zero #-}
bls12_381_G2_compressed_zero :: BuiltinByteString
bls12_381_G2_compressed_zero = BuiltinByteString BLS12_381.G2.compressed_zero

{-# NOINLINE bls12_381_G2_compressed_generator #-}
bls12_381_G2_compressed_generator :: BuiltinByteString
bls12_381_G2_compressed_generator = BuiltinByteString BLS12_381.G2.compressed_generator


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

{-# NOINLINE bls12_381_millerLoop #-}
bls12_381_millerLoop :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_MlResult
bls12_381_millerLoop (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G2_Element b) =
    BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.millerLoop a b

{-# NOINLINE bls12_381_mulMlResult #-}
bls12_381_mulMlResult :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult
bls12_381_mulMlResult (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b)
    = BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.mulMlResult a b

{-# NOINLINE bls12_381_finalVerify #-}
bls12_381_finalVerify ::  BuiltinBLS12_381_MlResult ->  BuiltinBLS12_381_MlResult -> BuiltinBool
bls12_381_finalVerify (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b)
    = BuiltinBool $ BLS12_381.Pairing.finalVerify a b

{-
CONVERSION
-}

{-# NOINLINE integerToByteString #-}
integerToByteString
    :: BuiltinBool
    -> BuiltinInteger
    -> BuiltinInteger
    -> BuiltinByteString
integerToByteString (BuiltinBool endiannessArg) paddingArg input =
  case Bitwise.integerToByteStringWrapper endiannessArg paddingArg input of
    BuiltinSuccess bs              -> BuiltinByteString bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ BuiltinByteString bs
    BuiltinFailure logs err        -> traceAll (logs <> pure (display err)) $
        Haskell.error "Integer to ByteString conversion errored."

{-# NOINLINE byteStringToInteger #-}
byteStringToInteger
    :: BuiltinBool
    -> BuiltinByteString
    -> BuiltinInteger
byteStringToInteger (BuiltinBool statedEndianness) (BuiltinByteString input) =
  Bitwise.byteStringToIntegerWrapper statedEndianness input

{-
BITWISE
-}

{-# NOINLINE shiftByteString #-}
shiftByteString ::
  BuiltinByteString ->
  BuiltinInteger ->
  BuiltinByteString
shiftByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.shiftByteString bs . fromIntegral

{-# NOINLINE rotateByteString #-}
rotateByteString ::
  BuiltinByteString ->
  BuiltinInteger ->
  BuiltinByteString
rotateByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.rotateByteString bs . fromIntegral

{-# NOINLINE countSetBits #-}
countSetBits ::
  BuiltinByteString ->
  BuiltinInteger
countSetBits (BuiltinByteString bs) = fromIntegral . Bitwise.countSetBits $ bs

{-# NOINLINE findFirstSetBit #-}
findFirstSetBit ::
  BuiltinByteString ->
  BuiltinInteger
findFirstSetBit (BuiltinByteString bs) =
  fromIntegral . Bitwise.findFirstSetBit $ bs

{-
LOGICAL
-}

{-# NOINLINE andByteString #-}
andByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
andByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.andByteString isPaddingSemantics data1 $ data2

{-# NOINLINE orByteString #-}
orByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
orByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.orByteString isPaddingSemantics data1 $ data2

{-# NOINLINE xorByteString #-}
xorByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
xorByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.xorByteString isPaddingSemantics data1 $ data2

{-# NOINLINE complementByteString #-}
complementByteString ::
  BuiltinByteString ->
  BuiltinByteString
complementByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.complementByteString $ bs

{-# NOINLINE readBit #-}
readBit ::
  BuiltinByteString ->
  BuiltinInteger ->
  BuiltinBool
readBit (BuiltinByteString bs) i =
  case Bitwise.readBit bs (fromIntegral i) of
    BuiltinFailure logs err -> traceAll (logs <> pure (display err)) $
      Haskell.error "readBit errored."
    BuiltinSuccess b -> BuiltinBool b
    BuiltinSuccessWithLogs logs b -> traceAll logs $ BuiltinBool b

{-# NOINLINE writeBits #-}
writeBits ::
  BuiltinByteString ->
  BuiltinList (BuiltinPair BuiltinInteger BuiltinBool) ->
  BuiltinByteString
writeBits (BuiltinByteString bs) (BuiltinList xs) =
  let unwrapped = fmap (\(BuiltinPair (i, BuiltinBool b)) -> (i, b)) xs in
    case Bitwise.writeBits bs unwrapped of
      BuiltinFailure logs err -> traceAll (logs <> pure (display err)) $
        Haskell.error "writeBits errored."
      BuiltinSuccess bs' -> BuiltinByteString bs'
      BuiltinSuccessWithLogs logs bs' -> traceAll logs $ BuiltinByteString bs'

{-# NOINLINE replicateByte #-}
replicateByte ::
  BuiltinInteger ->
  BuiltinInteger ->
  BuiltinByteString
replicateByte n w8 =
  case Bitwise.replicateByte n (fromIntegral w8) of
    BuiltinFailure logs err -> traceAll (logs <> pure (display err)) $
      Haskell.error "byteStringReplicate errored."
    BuiltinSuccess bs -> BuiltinByteString bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ BuiltinByteString bs
