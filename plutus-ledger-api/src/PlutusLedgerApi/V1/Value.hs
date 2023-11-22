-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

{-# OPTIONS_GHC -Wno-orphans #-}
-- Prevent unboxing, which the plugin can't deal with
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
-- We need -fexpose-all-unfoldings to compile the Marlowe validator
-- with GHC 9.6.2.
-- TODO. Look into this more closely: see PLT-7976.

-- | Functions for working with 'Value'.
module PlutusLedgerApi.V1.Value(
    -- ** Currency symbols
      CurrencySymbol(..)
    , currencySymbol
    , adaSymbol
    -- ** Token names
    , TokenName(..)
    , tokenName
    , toString
    , adaToken
    -- * Asset classes
    , AssetClass(..)
    , assetClass
    , assetClassValue
    , assetClassValueOf
    -- ** Value
    , Value(..)
    , singleton
    , valueOf
    , scale
    , symbols
      -- * Partial order operations
    , geq
    , gt
    , leq
    , lt
      -- * Etc.
    , isZero
    , split
    , unionWith
    , flattenValue
    ) where

import Prelude qualified as Haskell

import Control.DeepSeq (NFData)
import Data.ByteString qualified as BS
import Data.Data (Data)
import Data.String (IsString (fromString))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as E
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (LedgerBytes), encodeByteString)
import PlutusTx qualified
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Lift (makeLift)
import PlutusTx.Ord qualified as Ord
import PlutusTx.Prelude as PlutusTx hiding (sort)
import PlutusTx.These (These (..))
import Prettyprinter (Pretty, (<>))
import Prettyprinter.Extras (PrettyShow (PrettyShow))

{- | ByteString representing the currency, hashed with /BLAKE2b-224/.
It is empty for `Ada`, 28 bytes for `MintingPolicyHash`.
Forms an `AssetClass` along with `TokenName`.
A `Value` is a map from `CurrencySymbol`'s to a map from `TokenName` to an `Integer`.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://hydra.iohk.io/build/16861845/download/1/ledger-spec.pdf).
-}
newtype CurrencySymbol = CurrencySymbol { unCurrencySymbol :: PlutusTx.BuiltinByteString }
    deriving
        (IsString        -- ^ from hex encoding
        , Haskell.Show   -- ^ using hex encoding
        , Pretty         -- ^ using hex encoding
        ) via LedgerBytes
    deriving stock (Generic, Data)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving anyclass (NFData)

{-# INLINABLE currencySymbol #-}
-- | Creates `CurrencySymbol` from raw `ByteString`.
currencySymbol :: BS.ByteString -> CurrencySymbol
currencySymbol = CurrencySymbol . PlutusTx.toBuiltin

{- | ByteString of a name of a token.
Shown as UTF-8 string when possible.
Should be no longer than 32 bytes, empty for Ada.
Forms an `AssetClass` along with a `CurrencySymbol`.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://hydra.iohk.io/build/16861845/download/1/ledger-spec.pdf).
-}
newtype TokenName = TokenName { unTokenName :: PlutusTx.BuiltinByteString }
    deriving stock (Generic, Data)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving anyclass (NFData)
    deriving Pretty via (PrettyShow TokenName)

-- | UTF-8 encoding. Doesn't verify length.
instance IsString TokenName where
    fromString = fromText . Text.pack

{-# INLINABLE tokenName #-}
-- | Creates `TokenName` from raw `BS.ByteString`.
tokenName :: BS.ByteString -> TokenName
tokenName = TokenName . PlutusTx.toBuiltin

fromText :: Text -> TokenName
fromText = tokenName . E.encodeUtf8

fromTokenName :: (BS.ByteString -> r) -> (Text -> r) -> TokenName -> r
fromTokenName handleBytestring handleText (TokenName bs) = either (\_ -> handleBytestring $ PlutusTx.fromBuiltin bs) handleText $ E.decodeUtf8' (PlutusTx.fromBuiltin bs)

-- | Encode a `ByteString` to a hex `Text`.
asBase16 :: BS.ByteString -> Text
asBase16 bs = Text.concat ["0x", encodeByteString bs]

-- | Wrap the input `Text` in double quotes.
quoted :: Text -> Text
quoted s = Text.concat ["\"", s, "\""]

{- | Turn a TokenName to a hex-encoded 'String'

Compared to `show` , it will not surround the string with double-quotes.
-}
toString :: TokenName -> Haskell.String
toString = Text.unpack . fromTokenName asBase16 id

instance Haskell.Show TokenName where
    show = Text.unpack . fromTokenName asBase16 quoted

{-# INLINABLE adaSymbol #-}
-- | The 'CurrencySymbol' of the 'Ada' currency.
adaSymbol :: CurrencySymbol
adaSymbol = CurrencySymbol emptyByteString

{-# INLINABLE adaToken #-}
-- | The 'TokenName' of the 'Ada' currency.
adaToken :: TokenName
adaToken = TokenName emptyByteString

-- | An asset class, identified by a `CurrencySymbol` and a `TokenName`.
newtype AssetClass = AssetClass { unAssetClass :: (CurrencySymbol, TokenName) }
    deriving stock (Generic, Data)
    deriving newtype (Haskell.Eq, Haskell.Ord, Haskell.Show, Eq, Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving anyclass (NFData)
    deriving Pretty via (PrettyShow (CurrencySymbol, TokenName))

{-# INLINABLE assetClass #-}
-- | The curried version of 'AssetClass' constructor
assetClass :: CurrencySymbol -> TokenName -> AssetClass
assetClass s t = AssetClass (s, t)

{- | The 'Value' type represents a collection of amounts of different currencies.
We can think of 'Value' as a vector space whose dimensions are currencies.
To create a value of 'Value', we need to specify a currency. This can be done
using 'Ledger.Ada.adaValueOf'. To get the ada dimension of 'Value' we use
'Ledger.Ada.fromValue'. Plutus contract authors will be able to define modules
similar to 'Ledger.Ada' for their own currencies.

Operations on currencies are usually implemented /pointwise/. That is,
we apply the operation to the quantities for each currency in turn. So
when we add two 'Value's the resulting 'Value' has, for each currency,
the sum of the quantities of /that particular/ currency in the argument
'Value'. The effect of this is that the currencies in the 'Value' are "independent",
and are operated on separately.

Whenever we need to get the quantity of a currency in a 'Value' where there
is no explicit quantity of that currency in the 'Value', then the quantity is
taken to be zero.

There is no 'Ord Value' instance since 'Value' is only a partial order, so 'compare' can't
do the right thing in some cases.
 -}
newtype Value = Value { getValue :: Map.Map CurrencySymbol (Map.Map TokenName Integer) }
    deriving stock (Generic, Data, Haskell.Show)
    deriving anyclass (NFData)
    deriving newtype (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving Pretty via (PrettyShow Value)

instance Haskell.Eq Value where
    (==) = eq

instance Eq Value where
    {-# INLINABLE (==) #-}
    (==) = eq

instance Haskell.Semigroup Value where
    (<>) = unionWith (+)

instance Semigroup Value where
    {-# INLINABLE (<>) #-}
    (<>) = unionWith (+)

instance Haskell.Monoid Value where
    mempty = Value Map.empty

instance Monoid Value where
    {-# INLINABLE mempty #-}
    mempty = Value Map.empty

instance Group Value where
    {-# INLINABLE inv #-}
    inv = scale @Integer @Value (-1)

deriving via (Additive Value) instance AdditiveSemigroup Value
deriving via (Additive Value) instance AdditiveMonoid Value
deriving via (Additive Value) instance AdditiveGroup Value

instance Module Integer Value where
    {-# INLINABLE scale #-}
    scale i (Value xs) = Value (fmap (fmap (\i' -> i * i')) xs)

instance JoinSemiLattice Value where
    {-# INLINABLE (\/) #-}
    (\/) = unionWith Ord.max

instance MeetSemiLattice Value where
    {-# INLINABLE (/\) #-}
    (/\) = unionWith Ord.min

{-# INLINABLE valueOf #-}
-- | Get the quantity of the given currency in the 'Value'.
valueOf :: Value -> CurrencySymbol -> TokenName -> Integer
valueOf (Value mp) cur tn =
    case Map.lookup cur mp of
        Nothing -> 0 :: Integer
        Just i  -> case Map.lookup tn i of
            Nothing -> 0
            Just v  -> v

{-# INLINABLE symbols #-}
-- | The list of 'CurrencySymbol's of a 'Value'.
symbols :: Value -> [CurrencySymbol]
symbols (Value mp) = Map.keys mp

{-# INLINABLE singleton #-}
-- | Make a 'Value' containing only the given quantity of the given currency.
singleton :: CurrencySymbol -> TokenName -> Integer -> Value
singleton c tn i = Value (Map.singleton c (Map.singleton tn i))

{-# INLINABLE assetClassValue #-}
-- | A 'Value' containing the given amount of the asset class.
assetClassValue :: AssetClass -> Integer -> Value
assetClassValue (AssetClass (c, t)) i = singleton c t i

{-# INLINABLE assetClassValueOf #-}
-- | Get the quantity of the given 'AssetClass' class in the 'Value'.
assetClassValueOf :: Value -> AssetClass -> Integer
assetClassValueOf v (AssetClass (c, t)) = valueOf v c t

{-# INLINABLE unionVal #-}
-- | Combine two 'Value' maps
unionVal :: Value -> Value -> Map.Map CurrencySymbol (Map.Map TokenName (These Integer Integer))
unionVal (Value l) (Value r) =
    let
        combined = Map.union l r
        unThese k = case k of
            This a    -> This <$> a
            That b    -> That <$> b
            These a b -> Map.union a b
    in unThese <$> combined

{-# INLINABLE unionWith #-}
unionWith :: (Integer -> Integer -> Integer) -> Value -> Value -> Value
unionWith f ls rs =
    let
        combined = unionVal ls rs
        unThese k' = case k' of
            This a    -> f a 0
            That b    -> f 0 b
            These a b -> f a b
    in Value (fmap (fmap unThese) combined)

{-# INLINABLE flattenValue #-}
-- | Convert a value to a simple list, keeping only the non-zero amounts.
flattenValue :: Value -> [(CurrencySymbol, TokenName, Integer)]
flattenValue v = goOuter [] (Map.toList $ getValue v)
  where
    goOuter acc []             = acc
    goOuter acc ((cs, m) : tl) = goOuter (goInner cs acc (Map.toList m)) tl

    goInner _ acc [] = acc
    goInner cs acc ((tn, a) : tl)
        | a /= 0    = goInner cs ((cs, tn, a) : acc) tl
        | otherwise = goInner cs acc tl

-- Num operations

{-# INLINABLE isZero #-}
-- | Check whether a 'Value' is zero.
isZero :: Value -> Bool
isZero (Value xs) = Map.all (Map.all (\i -> 0 == i)) xs

{-# INLINABLE checkPred #-}
checkPred :: (These Integer Integer -> Bool) -> Value -> Value -> Bool
checkPred f l r =
    let
      inner :: Map.Map TokenName (These Integer Integer) -> Bool
      inner = Map.all f
    in
      Map.all inner (unionVal l r)

{-# INLINABLE checkBinRel #-}
-- | Check whether a binary relation holds for value pairs of two 'Value' maps,
--   supplying 0 where a key is only present in one of them.
checkBinRel :: (Integer -> Integer -> Bool) -> Value -> Value -> Bool
checkBinRel f l r =
    let
        unThese k' = case k' of
            This a    -> f a 0
            That b    -> f 0 b
            These a b -> f a b
    in checkPred unThese l r

{-# INLINABLE eq #-}
-- | Check whether one 'Value' is equal to another. See 'Value' for an explanation of how operations on 'Value's work.
eq :: Value -> Value -> Bool
-- If both are zero then checkBinRel will be vacuously true, but this is fine.
eq = checkBinRel (==)

{-# INLINABLE geq #-}
-- | Check whether one 'Value' is greater than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
geq :: Value -> Value -> Bool
-- If both are zero then checkBinRel will be vacuously true, but this is fine.
geq = checkBinRel (>=)

{-# INLINABLE leq #-}
-- | Check whether one 'Value' is less than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
leq :: Value -> Value -> Bool
-- If both are zero then checkBinRel will be vacuously true, but this is fine.
leq = checkBinRel (<=)

{-# INLINABLE gt #-}
-- | Check whether one 'Value' is strictly greater than another.
-- This is *not* a pointwise operation. @gt l r@ means @geq l r && not (eq l r)@.
gt :: Value -> Value -> Bool
gt l r = geq l r && not (eq l r)

{-# INLINABLE lt #-}
-- | Check whether one 'Value' is strictly less than another.
-- This is *not* a pointwise operation. @lt l r@ means @leq l r && not (eq l r)@.
lt :: Value -> Value -> Bool
lt l r = leq l r && not (eq l r)

-- | Split a value into its positive and negative parts. The first element of
--   the tuple contains the negative parts of the value, the second element
--   contains the positive parts.
--
--   @negate (fst (split a)) `plus` (snd (split a)) == a@
--
{-# INLINABLE split #-}
split :: Value -> (Value, Value)
split (Value mp) = (negate (Value neg), Value pos) where
  (neg, pos) = Map.mapThese splitIntl mp

  splitIntl :: Map.Map TokenName Integer -> These (Map.Map TokenName Integer) (Map.Map TokenName Integer)
  splitIntl mp' = These l r where
    (l, r) = Map.mapThese (\i -> if i <= 0 then This i else That i) mp'

makeLift ''CurrencySymbol
makeLift ''TokenName
makeLift ''AssetClass
makeLift ''Value
