{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}

module IsData.Budget.BuiltinCasing where

import IsData.Budget.Lib

import PlutusTx.Prelude

import PlutusTx.Builtins ()
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.IsData ()
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)
import System.FilePath qualified as Haskell
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)
import Prelude qualified as Haskell

decodeSingle :: CompiledCode (BuiltinData -> Integer)
decodeSingle =
  $$( compile
        [||\d -> case unsafeFromBuiltinData d of Single x -> x||]
    )

decodePair :: CompiledCode (BuiltinData -> Integer)
decodePair =
  $$( compile
        [||
        \d -> case unsafeFromBuiltinData d of
          PairA x -> x
          PairB x -> x + 1
        ||]
    )

decodeABC :: CompiledCode (BuiltinData -> Integer)
decodeABC =
  $$( compile
        [||
        \d -> case unsafeFromBuiltinData d of
          A x -> x
          B x -> x + 100
          C x -> x + 200
        ||]
    )

tests :: TestNested
tests =
  testNested ("IsData" Haskell.</> "Budget" Haskell.</> "BuiltinCasing")
    . Haskell.pure
    $ testNestedGhc
      [ goldenBundle "decodeSingle" decodeSingle (decodeSingle `unsafeApplyCode` inpSingle)
      , goldenBundle "decodePairA" decodePair (decodePair `unsafeApplyCode` inpPairA)
      , goldenBundle "decodePairB" decodePair (decodePair `unsafeApplyCode` inpPairB)
      , goldenBundle "decodeA" decodeABC (decodeABC `unsafeApplyCode` inpA)
      , goldenBundle "decodeC" decodeABC (decodeABC `unsafeApplyCode` inpC)
      ]
  where
    inpSingle = liftCodeDef (toBuiltinData (Single 99))
    inpPairA = liftCodeDef (toBuiltinData (PairA 10))
    inpPairB = liftCodeDef (toBuiltinData (PairB 20))
    inpA = liftCodeDef (toBuiltinData (A 42))
    inpC = liftCodeDef (toBuiltinData (C 7))
