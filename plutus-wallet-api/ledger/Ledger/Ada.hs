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

import           Ledger.Ada.TH
import           Prelude       hiding (negate)
