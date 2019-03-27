{-# LANGUAGE TemplateHaskell #-}

-- need orphan instances due to staging restriction
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Functions for working with 'Value' in Haskell.
module Ledger.Value(
      Value
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

import qualified Ledger.Value.TH as TH
import           Ledger.Value.TH (CurrencySymbol, Value)
import           Prelude         hiding (negate)

-- | Create a 'CurrencySymbol' from the given integer.
-- NOTE: this will use bytestrings to represent currencies in future.
currencySymbol :: Int -> CurrencySymbol
currencySymbol = $$(TH.currencySymbol)

instance Eq Value where
  (==) = $$(TH.eq)

instance Ord Value where
  (<=) = $$(TH.leq)

-- | See 'TH.singleton'.
singleton :: CurrencySymbol -> Int -> Value
singleton = $$(TH.singleton)

-- | See 'TH.valueOf'.
valueOf :: Value -> CurrencySymbol -> Int
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
