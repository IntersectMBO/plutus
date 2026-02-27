{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fforce-recomp #-}
-- {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
-- {-# OPTIONS_GHC -g #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-compilation-trace #-}

module AsData.Budget.Spec where

import Data.Proxy
import System.FilePath
import Test.Tasty.Extras

import AsData.Budget.Types
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Plugin.Utils
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)

tests :: TestNested
tests =
  testNested ("AsData" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "onlyUseFirstField" recordFields (recordFields `unsafeApplyCode` inp)
      ]

-- A function that only accesses the first field of `Ints`.
-- onlyUseFirstField :: CompiledCode (PlutusTx.BuiltinData -> Integer)
-- onlyUseFirstField = plinthc logic

recordFields :: CompiledCode (PlutusTx.BuiltinData -> Integer)
recordFields = plinthc logic

logic :: PlutusTx.BuiltinData -> Integer
logic d =
  let ints = PlutusTx.unsafeFromBuiltinData d
      x = int1 ints
      y = int2 ints
      z = int3 ints
      w = int4 ints
   in x
        `PlutusTx.addInteger` y
        `PlutusTx.addInteger` z
        `PlutusTx.addInteger` w
        `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                  (y `PlutusTx.addInteger` z)
                                  (x `PlutusTx.addInteger` w)
                                  then x `opaqueAdd` z
                                  else y `PlutusTx.addInteger` w
                              )
        `PlutusTx.addInteger` ( if PlutusTx.lessThanInteger
                                  (int3 ints `PlutusTx.addInteger` int2 ints)
                                  (int4 ints `PlutusTx.addInteger` int1 ints)
                                  then
                                    int3 ints
                                      `PlutusTx.addInteger` int1 ints
                                  else
                                    int4 ints
                                      `PlutusTx.addInteger` int2 ints
                              )

inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (Ints 10 20 30 40))

inpSum :: CompiledCode PlutusTx.BuiltinData
inpSum = liftCodeDef (PlutusTx.toBuiltinData (TheseD (Ints 10 20 30 40) (Ints 10 20 30 40)))

inpSumM :: CompiledCode PlutusTx.BuiltinData
inpSumM = liftCodeDef (PlutusTx.toBuiltinData (TheseDManual (Ints 10 20 30 40) (Ints 10 20 30 40)))
