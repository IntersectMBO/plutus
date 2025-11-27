{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -O1 #-}

module ShortCircuit.WithGHCOptimisations
  ( shortCircuitAnd
  , shortCircuitOr
  ) where

import PlutusTx.Prelude (error, (&&), (||))
import Prelude (Bool)

shortCircuitAnd :: Bool -> Bool
shortCircuitAnd x = x && error ()

shortCircuitOr :: Bool -> Bool
shortCircuitOr x = x || error ()
