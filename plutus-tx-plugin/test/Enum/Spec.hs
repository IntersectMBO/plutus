{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-optimize #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-beta #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-evaluate-builtins #-}

module Enum.Spec (tests) where

import PlutusTx.Plugin.Utils (plc)
import PlutusCore.Test (goldenUEval)
import PlutusTx
import PlutusTx.Prelude
import PlutusTx.Test (goldenPirReadable)
import Test.Tasty.Extras
import Data.Proxy

data SomeVeryLargeEnum
  = E1One
  | E2Two
  | E3Three
  | E4Four
  | E5Five
  | E6Six
  | E7Seven
  | E8Eight
  | E9Nine
  | E10Ten
deriveEnumData ''SomeVeryLargeEnum

tests :: TestNested
tests =
  testNested
    "Enum"
    [ testNestedGhc
        [ goldenPirReadable "SomeVeryLargeEnumData" someVeryLargeEnumData
        , goldenUEval "SomeVeryLargeEnumData" [someVeryLargeEnumData]
        , goldenPirReadable "methods" methods
        ]
    ]

someVeryLargeEnumData :: CompiledCode (Maybe SomeVeryLargeEnum)
someVeryLargeEnumData =
  -- result is constr 0 [constr 0] , because Just is 0 and E10Ten is alphabetically ordered as constructor 0
  -- See Note [Ordering of constructors]
  plc (Proxy @"someVeryLargeEnumData") (fromBuiltinData (toBuiltinData (unsafeFromBuiltinData @SomeVeryLargeEnum (toBuiltinData E10Ten))))

methods :: CompiledCode [Bool]
methods =
  plc (Proxy @"methods") (enumFromTo (pred (succ False)) (toEnum (fromEnum True)))
