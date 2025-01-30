-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}

-- This ensures that we don't put *anything* about these functions into the interface
-- file, otherwise GHC can be clever about the ones that are always error, even though
-- they're OPAQUE!
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
import Data.List qualified as Haskell
import Data.Text as Text (Text, empty)
import Data.Text.Encoding as Text (decodeUtf8, encodeUtf8)
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

-- See Note [Opaque builtin types]
data BuiltinBool = BuiltinBool ~Bool deriving stock Data

true :: BuiltinBool
true = BuiltinBool True
{-# OPAQUE true #-}

false :: BuiltinBool
false = BuiltinBool False
{-# OPAQUE false #-}

ifThenElse :: BuiltinBool -> a -> a -> a
ifThenElse (BuiltinBool b) x y = if b then x else y
{-# OPAQUE ifThenElse #-}

{-
UNIT
-}

-- See Note [Opaque builtin types]
data BuiltinUnit = BuiltinUnit ~() deriving stock Data

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

addInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
addInteger = coerce ((+) @Integer)
{-# OPAQUE addInteger #-}

subtractInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
subtractInteger = coerce ((-) @Integer)
{-# OPAQUE subtractInteger #-}

multiplyInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
multiplyInteger = coerce ((*) @Integer)
{-# OPAQUE multiplyInteger #-}

divideInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
divideInteger = coerce (div @Integer)
{-# OPAQUE divideInteger #-}

modInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
modInteger = coerce (mod @Integer)
{-# OPAQUE modInteger #-}

quotientInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
quotientInteger = coerce (quot @Integer)
{-# OPAQUE quotientInteger #-}

remainderInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
remainderInteger = coerce (rem @Integer)
{-# OPAQUE remainderInteger #-}

lessThanInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanInteger x y = BuiltinBool $ coerce ((<) @Integer) x  y
{-# OPAQUE lessThanInteger #-}

lessThanEqualsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanEqualsInteger x y = BuiltinBool $ coerce ((<=) @Integer) x y
{-# OPAQUE lessThanEqualsInteger #-}

equalsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
equalsInteger x y = BuiltinBool $ coerce ((==) @Integer) x y
{-# OPAQUE equalsInteger #-}

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

appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinByteString $ BS.append b1 b2
{-# OPAQUE appendByteString #-}

consByteString :: BuiltinInteger -> BuiltinByteString -> BuiltinByteString
consByteString n (BuiltinByteString b) = BuiltinByteString $ BS.cons (fromIntegral n) b
{-# OPAQUE consByteString #-}

sliceByteString :: BuiltinInteger -> BuiltinInteger -> BuiltinByteString -> BuiltinByteString
sliceByteString start n (BuiltinByteString b) = BuiltinByteString $ BS.take (fromIntegral n) (BS.drop (fromIntegral start) b)
{-# OPAQUE sliceByteString #-}

lengthOfByteString :: BuiltinByteString -> BuiltinInteger
lengthOfByteString (BuiltinByteString b) = toInteger $ BS.length b
{-# OPAQUE lengthOfByteString #-}

indexByteString :: BuiltinByteString -> BuiltinInteger -> BuiltinInteger
indexByteString (BuiltinByteString b) i = toInteger $ BS.index b (fromInteger i)
{-# OPAQUE indexByteString #-}

emptyByteString :: BuiltinByteString
emptyByteString = BuiltinByteString BS.empty
{-# OPAQUE emptyByteString #-}

sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha2_256 b
{-# OPAQUE sha2_256 #-}

sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha3_256 b
{-# OPAQUE sha3_256 #-}

blake2b_224 :: BuiltinByteString -> BuiltinByteString
blake2b_224 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_224 b
{-# OPAQUE blake2b_224 #-}

blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_256 b
{-# OPAQUE blake2b_256 #-}

keccak_256 :: BuiltinByteString -> BuiltinByteString
keccak_256 (BuiltinByteString b) = BuiltinByteString $ Hash.keccak_256 b
{-# OPAQUE keccak_256 #-}

ripemd_160 :: BuiltinByteString -> BuiltinByteString
ripemd_160 (BuiltinByteString b) = BuiltinByteString $ Hash.ripemd_160 b
{-# OPAQUE ripemd_160 #-}

verifyEd25519Signature :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> BuiltinBool
verifyEd25519Signature (BuiltinByteString vk) (BuiltinByteString msg) (BuiltinByteString sig) =
  case PlutusCore.Crypto.Ed25519.verifyEd25519Signature_V1 vk msg sig of
    BuiltinSuccess b              -> BuiltinBool b
    BuiltinSuccessWithLogs logs b -> traceAll logs $ BuiltinBool b
    BuiltinFailure logs err       -> traceAll (logs <> pure (display err)) $
        Haskell.error "Ed25519 signature verification errored."
{-# OPAQUE verifyEd25519Signature #-}

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
{-# OPAQUE verifyEcdsaSecp256k1Signature #-}

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
{-# OPAQUE verifySchnorrSecp256k1Signature #-}

traceAll :: forall (a :: Type) (f :: Type -> Type) .
  (Foldable f) => f Text -> a -> a
traceAll logs x = Foldable.foldl' (\acc t -> trace (BuiltinString t) acc) x logs

equalsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
equalsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 == b2
{-# OPAQUE equalsByteString #-}

lessThanByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 < b2
{-# OPAQUE lessThanByteString #-}

lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanEqualsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 <= b2
{-# OPAQUE lessThanEqualsByteString #-}

decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 (BuiltinByteString b) = BuiltinString $ Text.decodeUtf8 b
{-# OPAQUE decodeUtf8 #-}

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

appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString (BuiltinString s1) (BuiltinString s2) = BuiltinString (s1 <> s2)
{-# OPAQUE appendString #-}

emptyString :: BuiltinString
emptyString = BuiltinString Text.empty
{-# OPAQUE emptyString #-}

equalsString :: BuiltinString -> BuiltinString -> BuiltinBool
equalsString (BuiltinString s1) (BuiltinString s2) = BuiltinBool $ s1 == s2
{-# OPAQUE equalsString #-}

trace :: BuiltinString -> a -> a
trace _ x = x
{-# OPAQUE trace #-}

encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 (BuiltinString s) = BuiltinByteString $ Text.encodeUtf8 s
{-# OPAQUE encodeUtf8 #-}

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

fst :: BuiltinPair a b -> a
fst (BuiltinPair (a, _)) = a
{-# OPAQUE fst #-}

snd :: BuiltinPair a b -> b
snd (BuiltinPair (_, b)) = b
{-# OPAQUE snd #-}

mkPairData :: BuiltinData -> BuiltinData -> BuiltinPair BuiltinData BuiltinData
mkPairData d1 d2 = BuiltinPair (d1, d2)
{-# OPAQUE mkPairData #-}

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

null :: BuiltinList a -> BuiltinBool
null (BuiltinList (_:_)) = BuiltinBool False
null (BuiltinList [])    = BuiltinBool True
{-# OPAQUE null #-}

head :: BuiltinList a -> a
head (BuiltinList (x:_)) = x
head (BuiltinList [])    = Haskell.error "empty list"
{-# OPAQUE head #-}

tail :: BuiltinList a -> BuiltinList a
tail (BuiltinList (_:xs)) = BuiltinList xs
tail (BuiltinList [])     = Haskell.error "empty list"
{-# OPAQUE tail #-}

chooseList :: BuiltinList a -> b -> b -> b
chooseList (BuiltinList [])    b1 _ = b1
chooseList (BuiltinList (_:_)) _ b2 = b2
{-# OPAQUE chooseList #-}

drop :: Integer -> BuiltinList a -> BuiltinList a
drop i (BuiltinList xs) = BuiltinList (Haskell.genericDrop i xs)
{-# OPAQUE drop #-}

caseList' :: forall a r . r -> (a -> BuiltinList a -> r) -> BuiltinList a -> r
caseList' nilCase _        (BuiltinList [])       = nilCase
caseList' _       consCase (BuiltinList (x : xs)) = consCase x (BuiltinList xs)
{-# OPAQUE caseList' #-}

{-# NOINLINE drop #-}
drop :: Integer -> BuiltinList a -> BuiltinList a
drop i (BuiltinList xs) = BuiltinList (Haskell.genericDrop i xs)

{-# NOINLINE mkNilData #-}

mkNilData :: BuiltinUnit -> BuiltinList BuiltinData
mkNilData _ = BuiltinList []
{-# OPAQUE mkNilData #-}

mkNilPairData :: BuiltinUnit -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mkNilPairData _ = BuiltinList []
{-# OPAQUE mkNilPairData #-}

mkCons :: a -> BuiltinList a -> BuiltinList a
mkCons a (BuiltinList as) = BuiltinList (a:as)
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

-- NOT a builtin, only safe off-chain, hence the OPAQUE
-- | Convert a 'BuiltinData' into a 'PLC.Data'. Only works off-chain.
builtinDataToData :: BuiltinData -> PLC.Data
builtinDataToData (BuiltinData d) = d
{-# OPAQUE builtinDataToData #-}

-- NOT a builtin, only safe off-chain, hence the OPAQUE
-- | Convert a 'PLC.Data' into a 'BuiltinData'. Only works off-chain.
dataToBuiltinData :: PLC.Data -> BuiltinData
dataToBuiltinData = BuiltinData
{-# OPAQUE dataToBuiltinData #-}

chooseData :: forall a . BuiltinData -> a -> a -> a -> a -> a -> a
chooseData (BuiltinData d) constrCase mapCase listCase iCase bCase = case d of
    PLC.Constr{} -> constrCase
    PLC.Map{}    -> mapCase
    PLC.List{}   -> listCase
    PLC.I{}      -> iCase
    PLC.B{}      -> bCase
{-# OPAQUE chooseData #-}

caseData'
    :: (Integer -> BuiltinList BuiltinData -> r)
    -> (BuiltinList (BuiltinPair BuiltinData BuiltinData) -> r)
    -> (BuiltinList BuiltinData -> r)
    -> (Integer -> r)
    -> (BuiltinByteString -> r)
    -> BuiltinData
    -> r
caseData' constrCase mapCase listCase iCase bCase (BuiltinData d) = case d of
    PLC.Constr i ds -> constrCase i (BuiltinList (fmap dataToBuiltinData ds))
    PLC.Map ps      -> mapCase (BuiltinList (fmap p2p ps))
    PLC.List ds     -> listCase (BuiltinList (fmap dataToBuiltinData ds))
    PLC.I i         -> iCase i
    PLC.B b         -> bCase (BuiltinByteString b)
  where
    p2p (d1, d2) = BuiltinPair (dataToBuiltinData d1, dataToBuiltinData d2)
{-# OPAQUE caseData' #-}

mkConstr :: BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData
mkConstr i (BuiltinList args) = BuiltinData (PLC.Constr i (fmap builtinDataToData args))
{-# OPAQUE mkConstr #-}

mkMap :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData
mkMap (BuiltinList es) = BuiltinData (PLC.Map (fmap p2p es))
  where
      p2p (BuiltinPair (d, d')) = (builtinDataToData d, builtinDataToData d')
{-# OPAQUE mkMap #-}

mkList :: BuiltinList BuiltinData -> BuiltinData
mkList (BuiltinList l) = BuiltinData (PLC.List (fmap builtinDataToData l))
{-# OPAQUE mkList #-}

mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)
{-# OPAQUE mkI #-}

mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)
{-# OPAQUE mkB #-}

unsafeDataAsConstr :: BuiltinData -> BuiltinPair BuiltinInteger (BuiltinList BuiltinData)
unsafeDataAsConstr (BuiltinData (PLC.Constr i args)) = BuiltinPair (i, BuiltinList $ fmap dataToBuiltinData args)
unsafeDataAsConstr _                                 = Haskell.error "not a Constr"
{-# OPAQUE unsafeDataAsConstr #-}

unsafeDataAsMap :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
unsafeDataAsMap (BuiltinData (PLC.Map m)) = BuiltinList (fmap p2p m)
  where
      p2p (d, d') = BuiltinPair (dataToBuiltinData d, dataToBuiltinData d')
unsafeDataAsMap _                         = Haskell.error "not a Map"
{-# OPAQUE unsafeDataAsMap #-}

unsafeDataAsList :: BuiltinData -> BuiltinList BuiltinData
unsafeDataAsList (BuiltinData (PLC.List l)) = BuiltinList (fmap dataToBuiltinData l)
unsafeDataAsList _                          = Haskell.error "not a List"
{-# OPAQUE unsafeDataAsList #-}

unsafeDataAsI :: BuiltinData -> BuiltinInteger
unsafeDataAsI (BuiltinData (PLC.I i)) = i
unsafeDataAsI _                       = Haskell.error "not an I"
{-# OPAQUE unsafeDataAsI #-}

unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB (BuiltinData (PLC.B b)) = BuiltinByteString b
unsafeDataAsB _                       = Haskell.error "not a B"
{-# OPAQUE unsafeDataAsB #-}

equalsData :: BuiltinData -> BuiltinData -> BuiltinBool
equalsData (BuiltinData b1) (BuiltinData b2) = BuiltinBool $ b1 Haskell.== b2
{-# OPAQUE equalsData #-}

serialiseData :: BuiltinData -> BuiltinByteString
serialiseData (BuiltinData b) = BuiltinByteString $ BSL.toStrict $ serialise b
{-# OPAQUE serialiseData #-}


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

bls12_381_G1_equals :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBool
bls12_381_G1_equals a b = BuiltinBool $ coerce ((==) @BuiltinBLS12_381_G1_Element) a b
{-# OPAQUE bls12_381_G1_equals #-}

bls12_381_G1_add :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_add (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G1_Element b) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.add a b)
{-# OPAQUE bls12_381_G1_add #-}

bls12_381_G1_neg :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_neg (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.neg a)
{-# OPAQUE bls12_381_G1_neg #-}

bls12_381_G1_scalarMul :: BuiltinInteger -> BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element
bls12_381_G1_scalarMul n (BuiltinBLS12_381_G1_Element a) = BuiltinBLS12_381_G1_Element (BLS12_381.G1.scalarMul n a)
{-# OPAQUE bls12_381_G1_scalarMul #-}

bls12_381_G1_compress :: BuiltinBLS12_381_G1_Element -> BuiltinByteString
bls12_381_G1_compress (BuiltinBLS12_381_G1_Element a) = BuiltinByteString (BLS12_381.G1.compress a)
{-# OPAQUE bls12_381_G1_compress #-}

bls12_381_G1_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_uncompress (BuiltinByteString b) =
    case BLS12_381.G1.uncompress b of
      Left err -> Haskell.error $ "BSL12_381 G1 uncompression error: " ++ show err
      Right a  -> BuiltinBLS12_381_G1_Element a
{-# OPAQUE bls12_381_G1_uncompress #-}

bls12_381_G1_hashToGroup ::  BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G1_Element
bls12_381_G1_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
    case BLS12_381.G1.hashToGroup msg dst of
      Left err -> Haskell.error $ show err
      Right p  -> BuiltinBLS12_381_G1_Element p
{-# OPAQUE bls12_381_G1_hashToGroup #-}

bls12_381_G1_compressed_zero :: BuiltinByteString
bls12_381_G1_compressed_zero = BuiltinByteString BLS12_381.G1.compressed_zero
{-# OPAQUE bls12_381_G1_compressed_zero #-}

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

bls12_381_G2_equals :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBool
bls12_381_G2_equals a b = BuiltinBool $ coerce ((==) @BuiltinBLS12_381_G2_Element) a b
{-# OPAQUE bls12_381_G2_equals #-}

bls12_381_G2_add :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_add (BuiltinBLS12_381_G2_Element a) (BuiltinBLS12_381_G2_Element b) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.add a b)
{-# OPAQUE bls12_381_G2_add #-}

bls12_381_G2_neg :: BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_neg (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.neg a)
{-# OPAQUE bls12_381_G2_neg #-}

bls12_381_G2_scalarMul :: BuiltinInteger -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element
bls12_381_G2_scalarMul n (BuiltinBLS12_381_G2_Element a) = BuiltinBLS12_381_G2_Element (BLS12_381.G2.scalarMul n a)
{-# OPAQUE bls12_381_G2_scalarMul #-}

bls12_381_G2_compress :: BuiltinBLS12_381_G2_Element -> BuiltinByteString
bls12_381_G2_compress (BuiltinBLS12_381_G2_Element a) = BuiltinByteString (BLS12_381.G2.compress a)
{-# OPAQUE bls12_381_G2_compress #-}

bls12_381_G2_uncompress :: BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_uncompress (BuiltinByteString b) =
    case BLS12_381.G2.uncompress b of
      Left err -> Haskell.error $ "BSL12_381 G2 uncompression error: " ++ show err
      Right a  -> BuiltinBLS12_381_G2_Element a
{-# OPAQUE bls12_381_G2_uncompress #-}

bls12_381_G2_hashToGroup ::  BuiltinByteString -> BuiltinByteString -> BuiltinBLS12_381_G2_Element
bls12_381_G2_hashToGroup (BuiltinByteString msg) (BuiltinByteString dst) =
    case BLS12_381.G2.hashToGroup msg dst of
      Left err -> Haskell.error $ show err
      Right p  -> BuiltinBLS12_381_G2_Element p
{-# OPAQUE bls12_381_G2_hashToGroup #-}

bls12_381_G2_compressed_zero :: BuiltinByteString
bls12_381_G2_compressed_zero = BuiltinByteString BLS12_381.G2.compressed_zero
{-# OPAQUE bls12_381_G2_compressed_zero #-}

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

bls12_381_millerLoop :: BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_MlResult
bls12_381_millerLoop (BuiltinBLS12_381_G1_Element a) (BuiltinBLS12_381_G2_Element b) =
    BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.millerLoop a b
{-# OPAQUE bls12_381_millerLoop #-}

bls12_381_mulMlResult :: BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult
bls12_381_mulMlResult (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b)
    = BuiltinBLS12_381_MlResult $ BLS12_381.Pairing.mulMlResult a b
{-# OPAQUE bls12_381_mulMlResult #-}

bls12_381_finalVerify ::  BuiltinBLS12_381_MlResult ->  BuiltinBLS12_381_MlResult -> BuiltinBool
bls12_381_finalVerify (BuiltinBLS12_381_MlResult a) (BuiltinBLS12_381_MlResult b)
    = BuiltinBool $ BLS12_381.Pairing.finalVerify a b
{-# OPAQUE bls12_381_finalVerify #-}

{-
CONVERSION
-}

integerToByteString
    :: BuiltinBool
    -> BuiltinInteger
    -> BuiltinInteger
    -> BuiltinByteString
integerToByteString (BuiltinBool endiannessArg) paddingArg input =
  case Bitwise.integerToByteString endiannessArg paddingArg input of
    BuiltinSuccess bs              -> BuiltinByteString bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ BuiltinByteString bs
    BuiltinFailure logs err        -> traceAll (logs <> pure (display err)) $
        Haskell.error "Integer to ByteString conversion errored."
{-# OPAQUE integerToByteString #-}

byteStringToInteger
    :: BuiltinBool
    -> BuiltinByteString
    -> BuiltinInteger
byteStringToInteger (BuiltinBool statedEndianness) (BuiltinByteString input) =
  Bitwise.byteStringToInteger statedEndianness input
{-# OPAQUE byteStringToInteger #-}

{-
BITWISE
-}

shiftByteString ::
  BuiltinByteString ->
  BuiltinInteger ->
  BuiltinByteString
shiftByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.shiftByteString bs
{-# OPAQUE shiftByteString #-}

rotateByteString ::
  BuiltinByteString ->
  BuiltinInteger ->
  BuiltinByteString
rotateByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.rotateByteString bs
{-# OPAQUE rotateByteString #-}

countSetBits ::
  BuiltinByteString ->
  BuiltinInteger
countSetBits (BuiltinByteString bs) = fromIntegral . Bitwise.countSetBits $ bs
{-# OPAQUE countSetBits #-}

findFirstSetBit ::
  BuiltinByteString ->
  BuiltinInteger
findFirstSetBit (BuiltinByteString bs) =
  fromIntegral . Bitwise.findFirstSetBit $ bs
{-# OPAQUE findFirstSetBit #-}

{-
LOGICAL
-}

andByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
andByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.andByteString isPaddingSemantics data1 $ data2
{-# OPAQUE andByteString #-}

orByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
orByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.orByteString isPaddingSemantics data1 $ data2
{-# OPAQUE orByteString #-}

xorByteString ::
  BuiltinBool ->
  BuiltinByteString ->
  BuiltinByteString ->
  BuiltinByteString
xorByteString (BuiltinBool isPaddingSemantics) (BuiltinByteString data1) (BuiltinByteString data2) =
  BuiltinByteString . Bitwise.xorByteString isPaddingSemantics data1 $ data2
{-# OPAQUE xorByteString #-}

complementByteString ::
  BuiltinByteString ->
  BuiltinByteString
complementByteString (BuiltinByteString bs) =
  BuiltinByteString . Bitwise.complementByteString $ bs
{-# OPAQUE complementByteString #-}

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
{-# OPAQUE readBit #-}

writeBits ::
  BuiltinByteString ->
  BuiltinList BuiltinInteger ->
  BuiltinBool ->
  BuiltinByteString
writeBits (BuiltinByteString bs) (BuiltinList ixes) (BuiltinBool bit) =
  case Bitwise.writeBits bs ixes bit of
    BuiltinFailure logs err -> traceAll (logs <> pure (display err)) $
      Haskell.error "writeBits errored."
    BuiltinSuccess bs' -> BuiltinByteString bs'
    BuiltinSuccessWithLogs logs bs' -> traceAll logs $ BuiltinByteString bs'
{-# OPAQUE writeBits #-}

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
{-# OPAQUE replicateByte #-}

expModInteger ::
  BuiltinInteger ->
  BuiltinInteger ->
  BuiltinInteger ->
  BuiltinInteger
expModInteger b e m =
  -- (fromInteger @Rational) correctly throws an underflow exception upon negative integer
  -- both for GHC8.10 and GHC>=9
  case ExpMod.expMod b e (fromInteger m) of
    BuiltinFailure logs err -> traceAll (logs <> pure (display err)) $
      Haskell.error "expModInteger errored."
    BuiltinSuccess bs -> toInteger bs
    BuiltinSuccessWithLogs logs bs -> traceAll logs $ toInteger bs
{-# OPAQUE expModInteger #-}
