{-# LANGUAGE TemplateHaskell #-}

-- need orphan instances due to staging restriction
{-# OPTIONS_GHC -fno-warn-orphans #-}
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

currencySymbol :: Int -> CurrencySymbol
currencySymbol = $$(TH.currencySymbol)

instance Eq Value where
  (==) = $$(TH.eq)

instance Ord Value where
  (<=) = $$(TH.leq)

singleton :: CurrencySymbol -> Int -> Value
singleton = $$(TH.singleton)

valueOf :: Value -> CurrencySymbol -> Int
valueOf = $$(TH.valueOf)

scale :: Int -> Value -> Value
scale = $$(TH.scale)

zero :: Value
zero = $$(TH.zero)

plus :: Value -> Value -> Value
plus = $$(TH.plus)

minus :: Value -> Value -> Value
minus = $$(TH.minus)

multiply :: Value -> Value -> Value
multiply = $$(TH.multiply)

negate :: Value -> Value
negate = $$(TH.negate)

geq :: Value -> Value -> Bool
geq = $$(TH.geq)

gt :: Value -> Value -> Bool
gt = $$(TH.gt)

leq :: Value -> Value -> Bool
leq = $$(TH.leq)

lt :: Value -> Value -> Bool
lt = $$(TH.lt)

eq :: Value -> Value -> Bool
eq = $$(TH.eq)

isZero :: Value -> Bool
isZero = $$(TH.isZero)
