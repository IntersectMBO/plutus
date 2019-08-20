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
      Ada (..)
    , getAda
    , adaSymbol
    , adaToken
    -- * Constructors
    , fromValue
    , toValue
    , lovelaceOf
    , adaOf
    , lovelaceValueOf
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

import qualified Prelude                   as Haskell

import           Data.Fixed

import           Codec.Serialise.Class     (Serialise)
import           Data.Aeson                (FromJSON, ToJSON)
import           GHC.Generics              (Generic)
import           Language.PlutusTx.Lift    (makeLift)
import           Language.PlutusTx.Prelude hiding (divide, minus, multiply, negate, plus)
import qualified Language.PlutusTx.Prelude as P
import           Schema                    (ToSchema)

import           Ledger.Value              (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value              as TH

{-# INLINABLE adaSymbol #-}
-- | The 'CurrencySymbol' of the 'Ada' currency.
adaSymbol :: CurrencySymbol
adaSymbol = TH.currencySymbol emptyByteString

{-# INLINABLE adaToken #-}
-- | The 'TokenName' of the 'Ada' currency.
adaToken :: TokenName
adaToken = TH.tokenName emptyByteString

-- | ADA, the special currency on the Cardano blockchain. The unit of Ada is Lovelace, and
--   1M Lovelace is one Ada.
--   See note [Currencies] in 'Ledger.Validation.Value.TH'.
newtype Ada = Lovelace { getLovelace :: Integer }
    deriving (Enum)
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Eq, Ord, Num, Integral, Real, Serialise)

makeLift ''Ada

{-# INLINABLE getAda #-}
-- | Get the amount of Ada (the unit of the currency Ada) in this 'Ada' value.
getAda :: Ada -> Micro
getAda (Lovelace i) = MkFixed i

{-# INLINABLE toValue #-}
-- | Create a 'Value' containing only the given 'Ada'.
toValue :: Ada -> Value
toValue (Lovelace i) = TH.singleton adaSymbol adaToken i

{-# INLINABLE fromValue #-}
-- | Get the 'Ada' in the given 'Value'.
fromValue :: Value -> Ada
fromValue v = Lovelace (TH.valueOf v adaSymbol adaToken)

{-# INLINABLE lovelaceOf #-}
-- | Create 'Ada' representing the given quantity of Lovelace (the unit of the currency Ada).
lovelaceOf :: Integer -> Ada
lovelaceOf = Lovelace

{-# INLINABLE adaOf #-}
-- | Create 'Ada' representing the given quantity of Ada (1M Lovelace).
adaOf :: Micro -> Ada
adaOf (MkFixed x) = Lovelace x

{-# INLINABLE lovelaceValueOf #-}
-- | A 'Value' with the given amount of Lovelace (the currency unit).
--
--   @lovelaceValueOf == toValue . lovelaceOf@
--
lovelaceValueOf :: Integer -> Value
lovelaceValueOf = TH.singleton adaSymbol adaToken

{-# INLINABLE adaValueOf #-}
-- | A 'Value' with the given amount of Ada (the currency unit).
--
--   @adaValueOf == toValue . adaOf@
--
adaValueOf :: Micro -> Value
adaValueOf (MkFixed x) = TH.singleton adaSymbol adaToken x

{-# INLINABLE plus #-}
-- | Add two 'Ada' values together.
plus :: Ada -> Ada -> Ada
plus (Lovelace a) (Lovelace b) = Lovelace (P.plus a b)

{-# INLINABLE minus #-}
-- | Subtract one 'Ada' value from another.
minus :: Ada -> Ada -> Ada
minus (Lovelace a) (Lovelace b) = Lovelace (P.minus a b)

{-# INLINABLE multiply #-}
-- | Multiply two 'Ada' values together.
multiply :: Ada -> Ada -> Ada
multiply (Lovelace a) (Lovelace b) = Lovelace (P.multiply a b)

{-# INLINABLE divide #-}
-- | Divide one 'Ada' value by another.
divide :: Ada -> Ada -> Ada
divide (Lovelace a) (Lovelace b) = Lovelace (P.divide a b)

{-# INLINABLE zero #-}
-- | The zero 'Ada' value.
zero :: Ada
zero = Lovelace 0

{-# INLINABLE negate #-}
-- | Negate an 'Ada' value.
negate :: Ada -> Ada
negate (Lovelace i) = Lovelace (P.multiply (-1) i)

{-# INLINABLE isZero #-}
-- | Check whether an 'Ada' value is zero.
isZero :: Ada -> Bool
isZero (Lovelace i) = i == 0
