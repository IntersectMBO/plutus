{-# LANGUAGE TemplateHaskell #-}

-- need orphan instances due to staging restriction
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Functions for working with 'Value' in Haskell.
module Ledger.Value(
      Value
    , CurrencySymbol
    , currencySymbol
    , TokenName
    , tokenName
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

import qualified Ledger.Value.TH as TH
import           Ledger.Value.TH (CurrencySymbol, TokenName, Value)
import           Prelude         hiding (negate)
import qualified Language.PlutusTx.Prelude    as P

instance Eq Value where
  (==) = $$(TH.eq)

instance Ord Value where
  (<=) = $$(TH.leq)

instance Semigroup Value where
  (<>) = plus

instance Monoid Value where
  mempty = zero

currencySymbol :: P.ByteString -> CurrencySymbol
currencySymbol = $$(TH.currencySymbol)

tokenName :: P.ByteString -> TokenName
tokenName = $$(TH.tokenName)

-- | See 'TH.singleton'.
singleton :: CurrencySymbol -> TokenName -> Int -> Value
singleton = $$(TH.singleton)

-- | See 'TH.valueOf'.
valueOf :: Value -> CurrencySymbol -> TokenName -> Int
valueOf = $$(TH.valueOf)

-- | See 'TH.scale'.
scale :: Int -> Value -> Value
scale = $$(TH.scale)

-- | See 'TH.zero'.
zero :: Value
zero = $$(TH.zero)

-- | See 'TH.plus'.
plus :: Value -> Value -> Value
plus = $$(TH.plus)

-- | See 'TH.minus'.
minus :: Value -> Value -> Value
minus = $$(TH.minus)

-- | See 'TH.multiply'.
multiply :: Value -> Value -> Value
multiply = $$(TH.multiply)

-- | See 'TH.negate'.
negate :: Value -> Value
negate = $$(TH.negate)

-- | See 'TH.geq'.
geq :: Value -> Value -> Bool
geq = $$(TH.geq)

-- | See 'TH.gt'.
gt :: Value -> Value -> Bool
gt = $$(TH.gt)

-- | See 'TH.leq'.
leq :: Value -> Value -> Bool
leq = $$(TH.leq)

-- | See 'TH.lt'.
lt :: Value -> Value -> Bool
lt = $$(TH.lt)

-- | See 'TH.eq'.
eq :: Value -> Value -> Bool
eq = $$(TH.eq)

-- | See 'TH.isZero'.
isZero :: Value -> Bool
isZero = $$(TH.isZero)
