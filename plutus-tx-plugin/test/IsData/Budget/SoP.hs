{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=SumsOfProducts #-}

module IsData.Budget.SoP where

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

decodeMixed :: CompiledCode (BuiltinData -> Integer)
decodeMixed =
  $$( compile
        [||
        \d -> case unsafeFromBuiltinData d of
          MNone -> 0
          MOne x -> x
          MTwo x y -> x + y
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
  testNested ("IsData" Haskell.</> "Budget" Haskell.</> "SoP")
    . Haskell.pure
    $ testNestedGhc
      [ goldenBundle "decodeMixedNone" decodeMixed do
          decodeMixed `unsafeApplyCode` liftCodeDef (toBuiltinData MNone)
      , goldenBundle "decodeMixedTwo" decodeMixed do
          decodeMixed `unsafeApplyCode` liftCodeDef (toBuiltinData (MTwo 3 4))
      , goldenBundle "decodeSingle" decodeSingle do
          decodeSingle `unsafeApplyCode` liftCodeDef (toBuiltinData (Single 99))
      , goldenBundle "decodePairA" decodePair do
          decodePair `unsafeApplyCode` liftCodeDef (toBuiltinData (PairA 10))
      , goldenBundle "decodePairB" decodePair do
          decodePair `unsafeApplyCode` liftCodeDef (toBuiltinData (PairB 20))
      , goldenBundle "decodeA" decodeABC do
          decodeABC `unsafeApplyCode` liftCodeDef (toBuiltinData (A 42))
      , goldenBundle "decodeC" decodeABC do
          decodeABC `unsafeApplyCode` liftCodeDef (toBuiltinData (C 7))
      ]
