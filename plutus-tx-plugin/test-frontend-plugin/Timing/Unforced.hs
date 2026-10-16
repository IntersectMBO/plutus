{-# OPTIONS_GHC -ddump-timings #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}

-- | 'Timing.Terms' compiled with timing on and forcing off.
module Timing.Unforced (increment, choose) where

import Plinth.Plugin (plinthc)
import PlutusTx.Code (CompiledCode)
import Timing.Terms qualified as Terms

-- | 'Terms.increment' compiled with timing on and forcing off.
increment :: CompiledCode (Integer -> Integer)
increment = plinthc Terms.increment

-- | 'Terms.choose' compiled with timing on and forcing off.
choose :: CompiledCode (Bool -> Integer -> Integer)
choose = plinthc Terms.choose
