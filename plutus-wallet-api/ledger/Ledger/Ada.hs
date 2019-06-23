{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
-- Otherwise we get a complaint about the 'fromIntegral' call in the generated instance of 'Integral' for 'Ada'
{-# OPTIONS_GHC -Wno-identities #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | Functions for working with 'Ada' in Template Haskell.
module Ledger.Ada(
      Ada
    , adaSymbol
    , adaToken
    -- * Constructors
    , fromValue
    , fromInt
    , toValue
    , toInt
    , adaValueOf
    , zero
    -- * Num operations
    , plus
    , minus
    , multiply
    , divide
    , negate
    -- * Etc.
    , isZero
    ) where

import qualified Prelude                      as Haskell

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude    hiding (divide, minus, multiply, negate, plus)
import qualified Language.PlutusTx.Prelude    as P

import           Ledger.Value                 (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                 as TH

{-# INLINABLE adaSymbol #-}
-- | The 'CurrencySymbol' of the 'Ada' currency.
adaSymbol :: CurrencySymbol
adaSymbol = TH.currencySymbol emptyByteString

{-# INLINABLE adaToken #-}
-- | The 'TokenName' of the 'Ada' currency.
adaToken :: TokenName
adaToken = TH.tokenName emptyByteString

-- | ADA, the special currency on the Cardano blockchain.
--   See note [Currencies] in 'Ledger.Validation.Value.TH'.
newtype Ada = Ada { getAda :: Integer }
    deriving (Enum)
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Eq, Ord, Num, Integral, Real, Serialise)

makeLift ''Ada

{-# INLINABLE toValue #-}
-- | Create a 'Value' containing only the given 'Ada'.
toValue :: Ada -> Value
toValue (Ada i) = TH.singleton adaSymbol adaToken i

{-# INLINABLE fromValue #-}
-- | Get the 'Ada' in the given 'Value'.
fromValue :: Value -> Ada
fromValue v = Ada (TH.valueOf v adaSymbol adaToken)

{-# INLINABLE toInt #-}
-- | Get the amount of 'Ada'.
toInt :: Ada -> Integer
toInt (Ada i) = i

{-# INLINABLE fromInt #-}
-- | Turn a quantity into 'Ada'.
fromInt :: Integer -> Ada
fromInt = Ada

{-# INLINABLE adaValueOf #-}
-- | A 'Value' with the given amount of 'Ada'.
--
--   @adaValueOf == toValue . fromInt@
--
adaValueOf :: Integer -> Value
adaValueOf = TH.singleton adaSymbol adaToken

{-# INLINABLE plus #-}
-- | Add two 'Ada' values together.
plus :: Ada -> Ada -> Ada
plus (Ada a) (Ada b) = Ada (P.plus a b)

{-# INLINABLE minus #-}
-- | Subtract one 'Ada' value from another.
minus :: Ada -> Ada -> Ada
minus (Ada a) (Ada b) = Ada (P.minus a b)

{-# INLINABLE multiply #-}
-- | Multiply two 'Ada' values together.
multiply :: Ada -> Ada -> Ada
multiply (Ada a) (Ada b) = Ada (P.multiply a b)

{-# INLINABLE divide #-}
-- | Divide one 'Ada' value by another.
divide :: Ada -> Ada -> Ada
divide (Ada a) (Ada b) = Ada (P.divide a b)

{-# INLINABLE zero #-}
-- | The zero 'Ada' value.
zero :: Ada
zero = Ada 0

{-# INLINABLE negate #-}
-- | Negate an 'Ada' value.
negate :: Ada -> Ada
negate (Ada i) = Ada (P.multiply (-1) i)

{-# INLINABLE isZero #-}
-- | Check whether an 'Ada' value is zero.
isZero :: Ada -> Bool
isZero (Ada i) = i == 0
