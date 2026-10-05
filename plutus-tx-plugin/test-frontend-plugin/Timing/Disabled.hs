{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:no-dump-timings #-}

module Timing.Disabled (increment, choose) where

import Plinth.Plugin (plinthc)
import PlutusTx.Code (CompiledCode)
import Timing.Terms qualified as Terms

increment :: CompiledCode (Integer -> Integer)
increment = plinthc Terms.increment

choose :: CompiledCode (Bool -> Integer -> Integer)
choose = plinthc Terms.choose
