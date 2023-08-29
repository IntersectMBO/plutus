{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module Plugin.Optimization.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude as P
import PlutusTx.Test ()

import Data.Proxy

optimization :: TestNested
optimization = testNestedGhc "Optimization" [
    goldenUPlcCatch "alwaysSucceeds" alwaysSucceeds
  , goldenUPlcCatch "alwaysFails" alwaysFails
  ]

alwaysSucceeds :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
alwaysSucceeds = plc (Proxy @"alwaysSucceeds") (\_ _ _ -> ())

alwaysFails :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
alwaysFails = plc (Proxy @"alwaysFails") (\_ _ _ -> P.error ())
