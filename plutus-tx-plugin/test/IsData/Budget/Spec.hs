{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

-- NOTE: No datatypes=BuiltinCasing! This uses the default SumsOfProducts mode,
-- which is what real-world contracts on current mainnet use.

module IsData.Budget.Spec where

import IsData.Budget.Lib

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.IsData qualified as IsData
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)
import System.FilePath ((</>))
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

-- Decode from BuiltinData in default SoP mode.
-- This is where the regression manifests: the generated unsafeFromBuiltinData
-- uses caseInteger, which in SoP mode falls back to list indexing.
decodeABC :: CompiledCode (Builtins.BuiltinData -> Integer)
decodeABC =
  $$( compile
        [||
        \d -> case IsData.unsafeFromBuiltinData d of
          A x -> x
          B x -> x PlutusTx.+ 100
          C x -> x PlutusTx.+ 200
        ||]
    )

-- Input: A 42 encoded as BuiltinData (first constructor)
inpA :: CompiledCode Builtins.BuiltinData
inpA = liftCodeDef (IsData.toBuiltinData (A 42))

-- Input: C 7 encoded as BuiltinData (last constructor — worst case for list indexing)
inpC :: CompiledCode Builtins.BuiltinData
inpC = liftCodeDef (IsData.toBuiltinData (C 7))

tests :: TestNested
tests =
  testNested ("IsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "decodeA" decodeABC (decodeABC `unsafeApplyCode` inpA)
      , goldenBundle "decodeC" decodeABC (decodeABC `unsafeApplyCode` inpC)
      ]
