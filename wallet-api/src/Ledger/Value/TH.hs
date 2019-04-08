{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE LambdaCase         #-}
-- | Functions for working with 'Value' in Template Haskell.
module Ledger.Value.TH(
      Value(..)
    , CurrencySymbol
    , currencySymbol
    , singleton
    , valueOf
    , scale
      -- * Constants
    , zero
      -- * Num operations
    , plus
    , minus
    , multiply
    , negate
    , geq
    , gt
    , leq
    , lt
    , eq
      -- * Etc.
    , isZero
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, FromJSONKey, ToJSON, ToJSONKey, (.:))
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Extras            as JSON
import qualified Data.ByteString.Lazy         as BSL
import qualified Data.Swagger.Internal        as S
import           Data.Swagger.Schema          (ToSchema(declareNamedSchema), byteSchema)
import           GHC.Generics                 (Generic)
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import qualified Ledger.Map.TH                as Map
import qualified Ledger.These.TH              as These
import           Prelude                      hiding (all, lookup, negate)
import           LedgerBytes                  (LedgerBytes(LedgerBytes))

newtype CurrencySymbol = CurrencySymbol { unCurrencySymbol :: Builtins.SizedByteString 32 }
    deriving (Show, ToJSONKey, FromJSONKey, Serialise) via LedgerBytes
    deriving stock (Eq, Ord, Generic)

instance ToSchema CurrencySymbol where
  declareNamedSchema _ = pure $ S.NamedSchema (Just "CurrencySymbol") byteSchema

instance ToJSON CurrencySymbol where
  toJSON currencySymbol =
    JSON.object
      [ ( "unCurrencySymbol"
        , JSON.String .
          JSON.encodeByteString .
          BSL.toStrict . Builtins.unSizedByteString . unCurrencySymbol $
          currencySymbol)
      ]

instance FromJSON CurrencySymbol where
  parseJSON =
    JSON.withObject "CurrencySymbol" $ \object -> do
      raw <- object .: "unCurrencySymbol"
      bytes <- JSON.decodeByteString raw
      pure . CurrencySymbol . Builtins.SizedByteString . BSL.fromStrict $ bytes

makeLift ''CurrencySymbol

eqCurSymbol :: Q (TExp (CurrencySymbol -> CurrencySymbol -> Bool))
eqCurSymbol = [|| \(CurrencySymbol l) (CurrencySymbol r) -> $$(P.equalsByteString) l r ||]

currencySymbol :: Q (TExp (P.ByteString -> CurrencySymbol))
currencySymbol = [|| CurrencySymbol ||]

-- | A cryptocurrency value. This is a map from 'CurrencySymbol's to a
-- quantity of that currency.
--
-- Operations on currencies are usually implemented /pointwise/. That is,
-- we apply the operation to the quantities for each currency in turn. So
-- when we add two 'Value's the resulting 'Value' has, for each currency,
-- the sum of the quantities of /that particular/ currency in the argument
-- 'Value'. The effect of this is that the currencies in the 'Value' are "independent",
-- and are operated on separately.
--
-- Whenever we need to get the quantity of a currency in a 'Value' where there
-- is no explicit quantity of that currency in the 'Value', then the quantity is
-- taken to be zero.
--
-- See note [Currencies] for more details.
newtype Value = Value { getValue :: Map.Map CurrencySymbol Int }
    deriving (Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

makeLift ''Value

{- note [Currencies]

The 'Value' type represents a collection of amounts of different currencies.

We can think of 'Value' as a vector space whose dimensions are
currencies. At the moment there is only a single currency (Ada), so 'Value'
contains one-dimensional vectors. When currency-creating transactions are
implemented, this will change and the definition of 'Value' will change to a
'Map Currency Int', effectively a vector with infinitely many dimensions whose
non-zero values are recorded in the map.

To create a value of 'Value', we need to specifiy a currency. This can be done
using 'Ledger.Ada.adaValueOf'. To get the ada dimension of 'Value' we use
'Ledger.Ada.fromValue'. Plutus contract authors will be able to define modules
similar to 'Ledger.Ada' for their own currencies.

-}

-- | Get the quantity of the given currency in the 'Value'.
valueOf :: Q (TExp (Value -> CurrencySymbol -> Int))
valueOf = [||
  \(Value mp) cur ->
      case $$(Map.lookup) $$(eqCurSymbol) cur mp of
        Nothing -> 0 :: Int
        Just i  -> i
   ||]

-- | Make a 'Value' containing only the given quantity of the given currency.
singleton :: Q (TExp (CurrencySymbol -> Int -> Value))
singleton = [|| \c i -> Value ($$(Map.singleton) c i) ||]

unionWith :: Q (TExp ((Int -> Int -> Int) -> Value -> Value -> Value))
unionWith = [||
  \f (Value ls) (Value rs) ->
    let
        combined = $$(Map.union) $$(eqCurSymbol) ls rs
        unThese k = case k of
            Map.This a    -> f a 0
            Map.That b    -> f 0 b
            Map.These a b -> f a b
    in Value ($$(Map.map) unThese combined)
  ||]

-- | Multiply all the quantities in the 'Value' by the given scale factor.
scale :: Q (TExp (Int -> Value -> Value))
scale = [|| \i (Value xs) -> Value ($$(Map.map) (\i' -> $$(P.multiply) i i') xs) ||]

-- Num operations

-- | Add two 'Value's together. See 'Value' for an explanation of how operations on 'Value's work.
plus :: Q (TExp (Value -> Value -> Value))
plus = [|| $$(unionWith) $$(P.plus) ||]

-- | Negate a 'Value's. See 'Value' for an explanation of how operations on 'Value's work.
negate :: Q (TExp (Value -> Value))
negate = [|| $$(scale) (-1) ||]

-- | Subtract one 'Value' from another. See 'Value' for an explanation of how operations on 'Value's work.
minus :: Q (TExp (Value -> Value -> Value))
minus = [|| $$(unionWith) $$(P.minus) ||]

-- | Multiply two 'Value's together. See 'Value' for an explanation of how operations on 'Value's work.
multiply :: Q (TExp (Value -> Value -> Value))
multiply = [|| $$(unionWith) $$(P.multiply) ||]

-- | The empty 'Value'.
zero :: Q (TExp Value)
zero = [|| Value $$(Map.empty) ||]

-- | Check whether a 'Value' is zero.
isZero :: Q (TExp (Value -> Bool))
isZero = [|| \(Value xs) -> $$(Map.all) (\i -> $$(P.eq) 0 i) xs ||]

-- | Check whether one 'Value' is greater than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
geq :: Q (TExp (Value -> Value -> Bool))
geq = [||
  \(Value ls) (Value rs) ->
    let
        p = $$(These.theseWithDefault) 0 0 $$(P.geq)
    in
        $$(Map.all) p ($$(Map.union) $$(eqCurSymbol) ls rs) ||]

-- | Check whether one 'Value' is strictly greater than another. See 'Value' for an explanation of how operations on 'Value's work.
gt :: Q (TExp (Value -> Value -> Bool))
gt = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(These.theseWithDefault) 0 0 $$(P.gt)
    in
        $$(Map.all) p ($$(Map.union) $$(eqCurSymbol) ls rs) ||]

-- | Check whether one 'Value' is less than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
leq :: Q (TExp (Value -> Value -> Bool))
leq = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(These.theseWithDefault) 0 0 $$(P.leq)
    in
        $$(Map.all) p ($$(Map.union) $$(eqCurSymbol) ls rs) ||]

-- | Check whether one 'Value' is strictly less than another. See 'Value' for an explanation of how operations on 'Value's work.
lt :: Q (TExp (Value -> Value -> Bool))
lt = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(These.theseWithDefault) 0 0 $$(P.lt)
    in
        $$(Map.all) p ($$(Map.union) $$(eqCurSymbol) ls rs) ||]

-- | Check whether one 'Value' is equal to another. See 'Value' for an explanation of how operations on 'Value's work.
eq :: Q (TExp (Value -> Value -> Bool))
eq = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(These.theseWithDefault) 0 0 $$(P.eq)
    in
        $$(Map.all) p ($$(Map.union) $$(eqCurSymbol) ls rs) ||]
