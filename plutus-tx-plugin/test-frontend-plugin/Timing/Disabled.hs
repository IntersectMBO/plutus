{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-dump-timings #-}

-- | 'Timing.Terms' compiled with timing off.
module Timing.Disabled (increment, choose) where

import Plinth.Plugin (plinthc)
import PlutusTx.Code (CompiledCode)
import Timing.Terms qualified as Terms

-- | 'Terms.increment' compiled with timing off.
increment :: CompiledCode (Integer -> Integer)
increment = plinthc Terms.increment

-- | 'Terms.choose' compiled with timing off.
choose :: CompiledCode (Bool -> Integer -> Integer)
choose = plinthc Terms.choose
