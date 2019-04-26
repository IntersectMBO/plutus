{-# LANGUAGE TemplateHaskell #-}
-- | Functions for working with 'Ada' in Haskell.
module Ledger.Ada(
      Ada
      , adaSymbol
      , adaToken
      -- * Constructor
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
    ) where

import qualified Ledger.Ada.TH as TH
import           Ledger.Ada.TH (Ada)
import           Ledger.Value  (CurrencySymbol, TokenName, Value)
import           Prelude       hiding (negate)

-- | See 'TH.adaSymbol'
adaSymbol :: CurrencySymbol
adaSymbol = $$(TH.adaSymbol)

-- | See 'TH.adaToken'
adaToken :: TokenName
adaToken = $$(TH.adaToken)

-- | See 'TH.toValue'.
toValue :: Ada -> Value
toValue = $$(TH.toValue)

-- | See 'TH.fromValue'.
fromValue :: Value -> Ada
fromValue = $$(TH.fromValue)

-- | See 'TH.toInt'.
toInt :: Ada -> Int
toInt = $$(TH.toInt)

-- | See 'TH.fromInt'.
fromInt :: Int -> Ada
fromInt = $$(TH.fromInt)

-- | See 'TH.adaValueOf'.
adaValueOf :: Int -> Value
adaValueOf = $$(TH.adaValueOf)

-- | See 'TH.zero'.
zero :: Ada
zero = $$(TH.zero)

-- | See 'TH.plus'.
plus :: Ada -> Ada -> Ada
plus = $$(TH.plus)

-- | See 'TH.minus'.
minus :: Ada -> Ada -> Ada
minus = $$(TH.minus)

-- | See 'TH.multiply'.
multiply :: Ada -> Ada -> Ada
multiply = $$(TH.multiply)

-- | See 'TH.divide'.
divide :: Ada -> Ada -> Ada
divide = $$(TH.divide)

-- | See 'TH.negate'.
negate :: Ada -> Ada
negate = $$(TH.negate)

-- | See 'TH.geq'.
geq :: Ada -> Ada -> Bool
geq = $$(TH.geq)

-- | See 'TH.gt'.
gt :: Ada -> Ada -> Bool
gt = $$(TH.gt)

-- | See 'TH.leq'.
leq :: Ada -> Ada -> Bool
leq = $$(TH.leq)

-- | See 'TH.lt'.
lt :: Ada -> Ada -> Bool
lt = $$(TH.lt)

-- | See 'TH.eq'.
eq :: Ada -> Ada -> Bool
eq = $$(TH.eq)
