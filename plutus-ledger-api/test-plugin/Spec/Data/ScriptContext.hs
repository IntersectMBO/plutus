{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module Spec.Data.ScriptContext where

import Test.Tasty (TestTree)
import Test.Tasty.Extras

import PlutusLedgerApi.Data.V3 qualified as V3D
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestTree
tests =
  runTestNested ["test-plugin", "Spec", "Data", "ScriptContext"] . pure . testNestedGhc $
    [ goldenPirReadable "alwaysSucceeds" compiledAlwaysSucceeds
    , goldenUPlcReadable "alwaysSucceeds" compiledAlwaysSucceeds
    , goldenPirReadable "succeedsIfHasDatum" compiledSucceedsIfHasDatum
    , goldenUPlcReadable "succeedsIfHasDatum" compiledSucceedsIfHasDatum
    ]

alwaysSucceeds :: PlutusTx.BuiltinData -> PlutusTx.BuiltinUnit
alwaysSucceeds d =
  PlutusTx.check $
    case PlutusTx.unsafeFromBuiltinData d of
      V3D.ScriptContext _ _ _ -> True

succeedsIfHasDatum :: PlutusTx.BuiltinData -> PlutusTx.BuiltinUnit
succeedsIfHasDatum d =
  PlutusTx.check $
    case PlutusTx.unsafeFromBuiltinData d of
      V3D.ScriptContext _ _ (V3D.SpendingScript _ (Just _)) -> True
      _                                                     -> False

compiledAlwaysSucceeds :: CompiledCode (PlutusTx.BuiltinData -> PlutusTx.BuiltinUnit)
compiledAlwaysSucceeds = $$(compile [||alwaysSucceeds||])

compiledSucceedsIfHasDatum :: CompiledCode (PlutusTx.BuiltinData -> PlutusTx.BuiltinUnit)
compiledSucceedsIfHasDatum = $$(compile [||succeedsIfHasDatum||])
