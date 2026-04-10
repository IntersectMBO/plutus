{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module BuiltinList.NoCasing.Spec where

import PlutusTx.Prelude

import PlutusTx.BuiltinList qualified as L
import PlutusTx.Builtins qualified as B
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)
import System.FilePath ((</>))
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

tests :: TestNested
tests =
  testNested ("BuiltinList" </> "NoCasing")
    . pure
    $ testNestedGhc
      [ goldenBundle "unsafeUnconsOk" unsafeUnconsOk (unsafeUnconsOk `unsafeApplyCode` l1)
      ]

unsafeUnconsOk :: CompiledCode (L.BuiltinList Integer -> (Integer, L.BuiltinList Integer))
unsafeUnconsOk = $$(compile [||\xs -> B.unsafeUncons xs||])

l1 :: CompiledCode (L.BuiltinList Integer)
l1 = liftCodeDef $ toBuiltin ([1 .. 10] :: [Integer])
