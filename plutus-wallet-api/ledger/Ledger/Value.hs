-- need orphan instances due to staging restriction
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Functions for working with 'Value' in Haskell.
module Ledger.Value(
      Value(..)
    , CurrencySymbol(..)
    , currencySymbol
    , TokenName(..)
    , tokenName
    , singleton
    , valueOf
    , scale
    , symbols
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

import           Ledger.Value.TH
import           Prelude         hiding (negate)

instance Eq Value where
  (==) = eq

instance Ord Value where
  (<=) = leq

instance Semigroup Value where
  (<>) = plus

instance Monoid Value where
  mempty = zero
