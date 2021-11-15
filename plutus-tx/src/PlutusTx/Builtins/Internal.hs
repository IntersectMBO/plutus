{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE ImportQualifiedPost  #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- We don't want builtins getting torn apart. Enabling CPR analysis does that,
-- so we have to disable it. We leave worker/wrapper enabled, because that's
-- needed to give good compiled code here for off-chain use.
{-# OPTIONS_GHC -fno-cpr-anal #-}

-- | This module contains the special Haskell names that are used to map to builtin types or functions
-- in Plutus Core.
--
-- Most users should not use this module directly, but rather use 'PlutusTx.Builtins'.
module PlutusTx.Builtins.Internal where

import Codec.Serialise
import Control.DeepSeq (NFData)
import Crypto qualified
import Data.ByteArray qualified as BA
import Data.ByteString as BS
import Data.ByteString.Hash qualified as Hash
import Data.Coerce (coerce)
import Data.Hashable (Hashable (..))
import Data.Maybe (fromMaybe)
import Data.Text as Text (Text, empty)
import Data.Text.Encoding as Text (decodeUtf8, encodeUtf8)
import Data.Void (Void)
import GHC.Exts (lazy)
import GHC.Generics
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

-- We use GHC.Exts.lazy here so GHC can't see that the result is always bottom.
-- I (David Feuer) don't really understand why this is needed, but it seems to
-- be desired. We also don't allow this to be seen as strict in the unit,
-- because that would lead to a worker-wrapper transformation of `error`.
{-# NOINLINE error #-}
error :: BuiltinUnit -> a
error u = lazy u `seq` lazy (mustBeReplaced "error")

{-
BOOL
-}

newtype BuiltinBool = BuiltinBool Bool

{-# NOINLINE true #-}
true :: BuiltinBool
true = coerce True

{-# NOINLINE false #-}
false :: BuiltinBool
false = coerce False

{-# NOINLINE ifThenElse #-}
ifThenElse :: BuiltinBool -> a -> a -> a
ifThenElse (BuiltinBool b) x y = if b then x else y

{-
UNIT
-}

newtype BuiltinUnit = BuiltinUnit ()

{-# NOINLINE unitval #-}
unitval :: BuiltinUnit
unitval = BuiltinUnit ()

{-# NOINLINE chooseUnit #-}
chooseUnit :: BuiltinUnit -> a -> a
-- We allow only arity analysis of this function. No
-- demand analysis.
chooseUnit u a = lazy u `seq` lazy a

{-
INTEGER
-}

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
lessThanInteger = coerce ((<) @Integer)

{-# NOINLINE lessThanEqualsInteger #-}
lessThanEqualsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanEqualsInteger = coerce ((<=) @Integer)

{-# NOINLINE equalsInteger #-}
equalsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
equalsInteger = coerce ((==) @Integer)

{-
BYTESTRING
-}

{- Note [Silly sum types]

GHC's worker/wrapper transformation and CPR analysis really like to tear
product types apart. Usually, that's a good thing. But for our purposes, it's
not. We want to see the actual `BuiltinByteString` or `BuiltinString`, not its
constituent parts. So we turn these product types into sum types, by adding
constructors that can never actually be applied. Turning off CPR analysis in
this module and using `NOINLINE` where appropriate then seems to be sufficient
to prevent that. Anyone changing this stuff should be careful to inspect the
generated workers to make sure we're preserving everything we should.

Note: because the Void field in the NeverBS_ and NeverS_ constructors is
*strict*, GHC's pattern coverage checker recognizes that those constructors
aren't needed for complete pattern matches.
-}

-- | An opaque type representing Plutus Core ByteStrings.
data BuiltinByteString
  -- See Note [Silly sum types]
  -- This type *must* be defined in the same module as FakeBuiltinByteString.
  -- See Note [Building a custom Generic instance] for an explanation of that.
  = BuiltinByteString {-# UNPACK #-} !ByteString
  | NeverBS_ !Void
  deriving stock (Haskell.Eq, Haskell.Ord)
  deriving anyclass (NFData, Hashable, Serialise)

-- We define a custom Generic instance because we want any generic code working
-- with `BuiltinByteString` to see it as a single-constructor type. Most
-- importantly, any serialization should be done without a constructor tag.
--
-- See Note [Building a custom Generic instance]
instance Generic BuiltinByteString where
  type Rep BuiltinByteString = TwiddleBS (Rep FakeBuiltinByteString)
  {-# INLINE to #-}
  to (M1 (M1 (M1 (K1 bs)))) = BuiltinByteString bs
  {-# INLINE from #-}
  from (BuiltinByteString bs) = M1 (M1 (M1 (K1 bs)))

-- See Note [Building a custom Generic instance]
-- This type *must* be defined in the same module as BuiltinByteString.
data FakeBuiltinByteString = FakeBuiltinByteString {-# UNPACK #-} !ByteString
  deriving stock Generic

type family TwiddleBS fake where
  TwiddleBS (D1 ('MetaData _type_name mod_name pkg_name newtypeness)
             (C1 ('MetaCons _con_name x y)
               z)) =
           D1 ('MetaData "BuiltinByteString" mod_name pkg_name newtypeness)
             (C1 ('MetaCons "BuiltinByteString" x y)
               z)

{- Note [Building a custom Generic instance]

It's really easy to write custom `to` and `from` methods for `Generic`.  The
trickier part is getting the `Rep` right. The `Rep` includes metadata about
strictness, unpacking, constructor names, record selectors, etc. Some aspects
are difficult or impossible to get right manually, particularly the exact
package name and the "decided strictness". So instead of building the `Rep`
from scratch, we instead *edit* one that GHC builds us for a type,
FakeBuiltinByteString, that lives in the same module and looks almost identical
to the one we're trying to imitate. All we have to do is use a type family,
TwiddleBS, to edit the FakeBuiltinByteString to replace its type name and
constructor name with those of BuiltinByteString. All the other structural
information and metadata are copied over unchanged.
-}

instance Haskell.Show BuiltinByteString where
  showsPrec d (BuiltinByteString bs) = Haskell.showsPrec d bs

instance Haskell.Semigroup BuiltinByteString where
  BuiltinByteString bs1 <> BuiltinByteString bs2
    = BuiltinByteString $ bs1 Haskell.<> bs2

instance Haskell.Monoid BuiltinByteString where
  mempty = BuiltinByteString Haskell.mempty

instance Pretty BuiltinByteString where
    pretty = viaShow

instance BA.ByteArrayAccess BuiltinByteString where
  length (BuiltinByteString bs) = BA.length bs
  withByteArray (BuiltinByteString bs) = BA.withByteArray bs
  copyByteArrayToPtr (BuiltinByteString bs) = BA.copyByteArrayToPtr bs

instance BA.ByteArray BuiltinByteString where
  allocRet n f = do
    (a, bs) <- BA.allocRet n f
    pure (a, BuiltinByteString bs)

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
  coerce (fromMaybe False (Crypto.verifySignature pubKey message signature))

{-# NOINLINE equalsByteString #-}
equalsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
equalsByteString (BuiltinByteString b1) (BuiltinByteString b2) = coerce $ ((==) @ByteString) b1 b2

{-# NOINLINE lessThanByteString #-}
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanByteString (BuiltinByteString b1) (BuiltinByteString b2) = coerce $ ((<) @ByteString) b1 b2

{-# NOINLINE lessThanEqualsByteString #-}
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanEqualsByteString (BuiltinByteString b1) (BuiltinByteString b2) = coerce $ ((<=) @ByteString) b1 b2

{-# NOINLINE decodeUtf8 #-}
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 (BuiltinByteString b) = BuiltinString $ Text.decodeUtf8 b

{-
STRING
-}

data BuiltinString
  -- See Note [Silly sum types]
  = BuiltinString {-# UNPACK #-} !Text
  | NeverS_ !Void
    deriving stock (Haskell.Eq, Haskell.Ord)

instance Haskell.Show BuiltinString where
  showsPrec d (BuiltinString bs) = Haskell.showsPrec d bs

{-# NOINLINE appendString #-}
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString (BuiltinString s1) (BuiltinString s2) = BuiltinString (s1 <> s2)

{-# NOINLINE emptyString #-}
emptyString :: BuiltinString
emptyString = BuiltinString Text.empty

{-# NOINLINE equalsString #-}
equalsString :: BuiltinString -> BuiltinString -> BuiltinBool
equalsString (BuiltinString s1) (BuiltinString s2) = coerce $ ((==) @Text) s1 s2

{-# NOINLINE trace #-}
trace :: BuiltinString -> a -> a
trace _ x = x

{-# NOINLINE encodeUtf8 #-}
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 (BuiltinString s) = BuiltinByteString $ Text.encodeUtf8 s

{-
PAIR
-}

newtype BuiltinPair a b = BuiltinPair (a, b)
    deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)

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

newtype BuiltinList a = BuiltinList [a]
    deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)

{-# NOINLINE null #-}
null :: BuiltinList a -> BuiltinBool
null (BuiltinList (_:_)) = coerce False
null (BuiltinList [])    = coerce True

{-# NOINLINE head #-}
head :: BuiltinList a -> a
head (BuiltinList (x:_)) = x
head (BuiltinList [])    = Haskell.error "empty list"

{-# NOINLINE tail #-}
tail :: BuiltinList a -> BuiltinList a
tail (BuiltinList (_:xs)) = coerce xs
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
newtype BuiltinData = BuiltinData PLC.Data
    deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)

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
mkConstr i args = BuiltinData (PLC.Constr i (coerce args))

{-# NOINLINE mkMap #-}
mkMap :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData
mkMap es = BuiltinData (PLC.Map (coerce es))

{-# NOINLINE mkList #-}
mkList :: BuiltinList BuiltinData -> BuiltinData
mkList l = BuiltinData (PLC.List (coerce l))

{-# NOINLINE mkI #-}
mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)

{-# NOINLINE mkB #-}
mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)

{-# NOINLINE unsafeDataAsConstr #-}
unsafeDataAsConstr :: BuiltinData -> BuiltinPair BuiltinInteger (BuiltinList BuiltinData)
unsafeDataAsConstr (BuiltinData (PLC.Constr i args)) = BuiltinPair (i, coerce args)
unsafeDataAsConstr _                                 = Haskell.error "not a Constr"

{-# NOINLINE unsafeDataAsMap #-}
unsafeDataAsMap :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
unsafeDataAsMap (BuiltinData (PLC.Map m)) = coerce m
unsafeDataAsMap _                         = Haskell.error "not a Map"

{-# NOINLINE unsafeDataAsList #-}
unsafeDataAsList :: BuiltinData -> BuiltinList BuiltinData
unsafeDataAsList (BuiltinData (PLC.List l)) = coerce l
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
equalsData (BuiltinData b1) (BuiltinData b2) = coerce $ b1 Haskell.== b2
