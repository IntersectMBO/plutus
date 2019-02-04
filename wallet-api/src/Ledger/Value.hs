{-# LANGUAGE TemplateHaskell #-}
module Ledger.Value(
      Value
      -- * Constants
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
    , size
    ) where

import qualified Ledger.Value.TH as TH
import           Ledger.Value.TH (Value)
import           Prelude         hiding (negate)

zero :: Value
zero = $$(TH.zero)

plus :: Value -> Value -> Value
plus = $$(TH.plus)

minus :: Value -> Value -> Value
minus = $$(TH.minus)

multiply :: Value -> Value -> Value
multiply = $$(TH.multiply)

divide :: Value -> Value -> Value
divide = $$(TH.divide)

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

size :: Value -> Int
size = $$(TH.size)
