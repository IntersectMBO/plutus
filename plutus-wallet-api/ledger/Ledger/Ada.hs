{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
-- Otherwise we get a complaint about the 'fromIntegral' call in the generated instance of 'Integral' for 'Ada'
{-# OPTIONS_GHC -Wno-identities #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
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
    , geq
    , gt
    , leq
    , lt
    , eq
    -- * Etc.
    , isZero
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude    hiding (divide, eq, geq, gt, leq, lt, minus, multiply, negate, plus)
import qualified Language.PlutusTx.Prelude    as P

import           Ledger.Value                 (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                 as TH

-- | The 'CurrencySymbol' of the 'Ada' currency.
adaSymbol :: CurrencySymbol
adaSymbol = TH.currencySymbol emptyByteString

-- | The 'TokenName' of the 'Ada' currency.
adaToken :: TokenName
adaToken = TH.tokenName emptyByteString

-- | ADA, the special currency on the Cardano blockchain.
--   See note [Currencies] in 'Ledger.Validation.Value.TH'.
newtype Ada = Ada { getAda :: Integer }
    deriving (Eq, Ord, Show, Enum)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Num, Integral, Real, Serialise)

makeLift ''Ada

-- | Create a 'Value' containing only the given 'Ada'.
toValue :: Ada -> Value
toValue (Ada i) = TH.singleton adaSymbol adaToken i

-- | Get the 'Ada' in the given 'Value'.
fromValue :: Value -> Ada
fromValue v = Ada (TH.valueOf v adaSymbol adaToken)

-- | Get the amount of 'Ada'.
toInt :: Ada -> Integer
toInt (Ada i) = i

-- | Turn a quantity into 'Ada'.
fromInt :: Integer -> Ada
fromInt = Ada

-- | A 'Value' with the given amount of 'Ada'.
--
--   @adaValueOf == toValue . fromInt@
--
adaValueOf :: Integer -> Value
adaValueOf = TH.singleton adaSymbol adaToken

-- | Add two 'Ada' values together.
plus :: Ada -> Ada -> Ada
plus (Ada a) (Ada b) = Ada (P.plus a b)

-- | Subtract one 'Ada' value from another.
minus :: Ada -> Ada -> Ada
minus (Ada a) (Ada b) = Ada (P.minus a b)

-- | Multiply two 'Ada' values together.
multiply :: Ada -> Ada -> Ada
multiply (Ada a) (Ada b) = Ada (P.multiply a b)

-- | Divide one 'Ada' value by another.
divide :: Ada -> Ada -> Ada
divide (Ada a) (Ada b) = Ada (P.divide a b)

-- | The zero 'Ada' value.
zero :: Ada
zero = Ada 0

-- | Negate an 'Ada' value.
negate :: Ada -> Ada
negate (Ada i) = Ada (P.multiply (-1) i)

-- | Check whether an 'Ada' value is zero.
isZero :: Ada -> Bool
isZero (Ada i) = P.eq i 0

-- | Check whether one 'Ada' is greater than or equal to another.
geq :: Ada -> Ada -> Bool
geq (Ada i) (Ada j) = P.geq i j

-- | Check whether one 'Ada' is strictly greater than another.
gt :: Ada -> Ada -> Bool
gt (Ada i) (Ada j) = P.gt i j

-- | Check whether one 'Ada' is less than or equal to another.
leq :: Ada -> Ada -> Bool
leq (Ada i) (Ada j) = P.leq i j

-- | Check whether one 'Ada' is strictly less than another.
lt :: Ada -> Ada -> Bool
lt (Ada i) (Ada j) = P.lt i j

-- | Check whether one 'Ada' is equal to another.
eq :: Ada -> Ada -> Bool
eq (Ada i) (Ada j) = P.eq i j
