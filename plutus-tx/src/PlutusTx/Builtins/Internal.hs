{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
-- This ensures that we don't put *anything* about these functions into the interface
-- file, otherwise GHC can be clever about the ones that are always error, even though
-- they're NOINLINE!
{-# OPTIONS_GHC -O0 #-}
-- | This module contains the special Haskell names that are used to map to builtin types or functions
-- in Plutus Core.
--
-- Most users should not use this module directly, but rather use 'PlutusTx.Builtins'.
module PlutusTx.Builtins.Internal where

import Codec.Serialise
import Control.DeepSeq (NFData (..))
import Crypto qualified
import Data.ByteArray qualified as BA
import Data.ByteString as BS
import Data.ByteString.Hash qualified as Hash
import Data.Coerce (coerce)
import Data.Hashable (Hashable (..))
import Data.Maybe (fromMaybe)
import Data.Text as Text (Text, empty)
import Data.Text.Encoding as Text (decodeUtf8, encodeUtf8)
import PlutusCore.Data qualified as PLC
import PlutusTx.Utils (mustBeReplaced)
import Prettyprinter (Pretty (..), viaShow)

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
error = mustBeReplaced "error"

{-
BOOL
-}

-- See Note [Opaque builtin types]
data BuiltinBool = BuiltinBool Bool

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
data BuiltinUnit = BuiltinUnit ()

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
data BuiltinByteString = BuiltinByteString ByteString

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
sha2_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha2 b

{-# NOINLINE sha3_256 #-}
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 (BuiltinByteString b) = BuiltinByteString $ Hash.sha3 b

{-# NOINLINE blake2b_256 #-}
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b b

{-# NOINLINE verifySignature #-}
verifySignature :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> BuiltinBool
verifySignature (BuiltinByteString pubKey) (BuiltinByteString message) (BuiltinByteString signature) =
  BuiltinBool (fromMaybe False (Crypto.verifySignature pubKey message signature))

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
data BuiltinString = BuiltinString Text

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
data BuiltinPair a b = BuiltinPair (a, b)

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
data BuiltinList a = BuiltinList [a]

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
chooseList :: BuiltinList a -> b -> b-> b
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
data BuiltinData = BuiltinData PLC.Data

instance Haskell.Show BuiltinData where
    show (BuiltinData d) = show d
instance Haskell.Eq BuiltinData where
    (==) (BuiltinData d) (BuiltinData d') = (==) d d'
instance Haskell.Ord BuiltinData where
    compare (BuiltinData d) (BuiltinData d') = compare d d'

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
mkMap (BuiltinList es) = BuiltinData (PLC.Map $ (fmap p2p es))
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
