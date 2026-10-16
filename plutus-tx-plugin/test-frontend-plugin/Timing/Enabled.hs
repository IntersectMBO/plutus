{-# OPTIONS_GHC -ddump-timings #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:force-timings #-}

-- | 'Timing.Terms' compiled with timing and forcing on.
module Timing.Enabled (increment, choose) where

import Plinth.Plugin (plinthc)
import PlutusTx.Code (CompiledCode)
import Timing.Terms qualified as Terms

-- | 'Terms.increment' compiled with timing and forcing on.
increment :: CompiledCode (Integer -> Integer)
increment = plinthc Terms.increment

-- | 'Terms.choose' compiled with timing and forcing on.
choose :: CompiledCode (Bool -> Integer -> Integer)
choose = plinthc Terms.choose
