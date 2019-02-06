{-# LANGUAGE TemplateHaskell #-}
module Ledger.Ada(
      Ada
      -- * Constructor
      , fromValue
      , fromInt
      , toValue
      , toInt
      , adaValueOf
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
    ) where

import qualified Ledger.Ada.TH as TH
import           Ledger.Ada.TH (Ada)
import           Ledger.Value  (Value)
import           Prelude       hiding (negate)

toValue :: Ada -> Value
toValue = $$(TH.toValue)

fromValue :: Value -> Ada
fromValue = $$(TH.fromValue)

toInt :: Ada -> Int
toInt = $$(TH.toInt)

fromInt :: Int -> Ada
fromInt = $$(TH.fromInt)

adaValueOf :: Int -> Value
adaValueOf = $$(TH.adaValueOf)

plus :: Ada -> Ada -> Ada
plus = $$(TH.plus)

minus :: Ada -> Ada -> Ada
minus = $$(TH.minus)

multiply :: Ada -> Ada -> Ada
multiply = $$(TH.multiply)

divide :: Ada -> Ada -> Ada
divide = $$(TH.divide)

negate :: Ada -> Ada
negate = $$(TH.negate)

geq :: Ada -> Ada -> Bool
geq = $$(TH.geq)

gt :: Ada -> Ada -> Bool
gt = $$(TH.gt)

leq :: Ada -> Ada -> Bool
leq = $$(TH.leq)

lt :: Ada -> Ada -> Bool
lt = $$(TH.lt)

eq :: Ada -> Ada -> Bool
eq = $$(TH.eq)
