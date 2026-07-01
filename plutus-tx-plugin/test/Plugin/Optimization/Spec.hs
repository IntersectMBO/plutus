{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Plugin.Optimization.Spec where

import Test.Tasty.Extras

import Plinth.Plugin
import PlutusCore.Test
import PlutusTx.Code
import PlutusTx.Prelude as P
import PlutusTx.Test ()

optimization :: TestNested
optimization =
  testNested "Optimization" Prelude.. Prelude.pure Prelude.$
    testNestedGhc
      [ goldenUPlc "alwaysSucceeds" alwaysSucceeds
      , goldenUPlc "alwaysFails" alwaysFails
      ]

alwaysSucceeds :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
alwaysSucceeds = plinthc (\_ _ _ -> ())

alwaysFails :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
alwaysFails = plinthc (\_ _ _ -> P.error ())
