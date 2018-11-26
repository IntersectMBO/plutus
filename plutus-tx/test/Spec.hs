{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Most tests for this functionality are in the plugin package, this is mainly just checking that the wiring machinery
-- works.
module Main (main) where

import           Common
import           PlcTestUtils

import           TestTH

import           Language.PlutusTx.TH
import           Language.PlutusTx.Prelude

import           Language.PlutusCore.Interpreter.CekMachine
import           Language.PlutusCore.Pretty
import           Language.PlutusCore
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Constant

import Control.Monad.Except
import Control.Exception

import           Test.Tasty

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance GetProgram PlcCode where
    getProgram = catchAll . getAst

dynamicBuiltins :: DynamicBuiltinNameMeanings
dynamicBuiltins =
    insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $ insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

runPlcCek :: GetProgram a => [a] -> ExceptT SomeException IO EvaluationResult
runPlcCek values = do
     ps <- traverse getProgram values
     let p = foldl1 applyProgram ps
     catchAll $ runCek dynamicBuiltins p

goldenEvalCek :: GetProgram a => String -> [a] -> TestNested
goldenEvalCek name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runPlcCek values)

tests :: TestNested
tests = testGroup "plutus-th" <$> sequence [
    goldenPlc "simple" simple
    , goldenPlc "power" powerPlc
    , goldenPlc "and" andPlc
    , goldenEvalCek "convertString" [convertString]
  ]

simple :: PlcCode
simple = $$(plutus [|| \(x::Bool) -> if x then (1::Int) else (2::Int) ||])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: PlcCode
powerPlc = $$(plutus [|| $$(power (4::Int)) ||])

andPlc :: PlcCode
andPlc = $$(plutus [|| $$(andTH) True False ||])

convertString :: PlcCode
convertString = $$(plutus [|| $$(toPlutusString) "test" ||])
