{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module ShortCircuit.WithoutGHCOptimisations
  ( shortCircuitAnd
  , shortCircuitOr
  ) where

import PlutusTx.Prelude (error, (&&), (||))
import Prelude (Bool)

shortCircuitAnd :: Bool -> Bool
shortCircuitAnd x = x && error ()

shortCircuitOr :: Bool -> Bool
shortCircuitOr x = x || error ()
