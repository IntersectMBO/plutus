{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-optimize #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-beta #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-simplifier-evaluate-builtins #-}

module Bounded.Spec where

import PlutusTx
import PlutusTx.Test (goldenPirReadable)
import Test.Tasty.Extras
import PlutusTx.Bounded
import PlutusTx.Prelude
import PlutusTx.Plugin (plc)
import Data.Proxy (Proxy (..))

data SomeVeryLargeEnum
  = E1
  | E2
  | E3
  | E4
  | E5
  | E6
  | E7
  | E8
  | E9
  | E10
deriveBounded ''SomeVeryLargeEnum

data SingleConstructor a = SingleConstructor Bool a ()
deriveBounded ''SingleConstructor

newtype PhantomADT e = PhantomADT ()
deriveBounded ''PhantomADT

minAndMax :: Bounded a => (a, a)
minAndMax = (minBound,maxBound)

compiledSomeVeryLargeEnum :: CompiledCode (SomeVeryLargeEnum, SomeVeryLargeEnum)
compiledSomeVeryLargeEnum = plc (Proxy @"compiledSomeVeryLargeEnum") minAndMax

compiledSingleConstructor :: CompiledCode (SingleConstructor Ordering, SingleConstructor Ordering)
compiledSingleConstructor = plc (Proxy @"compiledSingleConstructor") minAndMax

{- here cannot use Ordering or Either as the phantom type because of
pir compile error (unrelated to Bounded):
GHC Core to PLC plugin: Error: Error from the PIR compiler:
Error during compilation: Type bindings cannot appear in recursive let, use datatypebind instead
See https://github.com/IntersectMBO/plutus/issues/7498
-}
compiledPhantomADT :: CompiledCode (PhantomADT Bool, PhantomADT Bool)
compiledPhantomADT = plc (Proxy @"compiledPhantomADT") minAndMax

tests :: TestNested
tests =
  testNested
    "Bounded"
    [ testNestedGhc
        [ goldenPirReadable "SomeVeryLargeEnum" compiledSomeVeryLargeEnum
        , goldenPirReadable "SingleConstructor" compiledSingleConstructor
        , goldenPirReadable "PhantomADT" compiledPhantomADT
        ]
    ]
