{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC   -g #-}

module TH.Spec (tests) where

import           Common
import           PlcTestUtils

import           TH.TestTH

import qualified Prelude as Haskell

import           Language.PlutusTx.TH
import           Language.PlutusTx.Code
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.Evaluation
import           Language.PlutusTx

import qualified Language.PlutusIR          as PIR

import           Language.PlutusCore.Pretty
import           Language.PlutusCore

import           Control.Monad.Except
import           Control.Exception

import           Data.Text.Prettyprint.Doc
import           Test.Tasty

instance GetProgram (CompiledCode a) where
    getProgram = catchAll . getPlc

goldenPir :: String -> CompiledCode a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value

runPlcCek :: GetProgram a => [a] -> ExceptT SomeException IO EvaluationResultDef
runPlcCek values = do
     ps <- Haskell.traverse getProgram values
     let p = foldl1 applyProgram ps
     either (throwError . SomeException) Haskell.pure $ evaluateCek p

runPlcCekTrace :: GetProgram a => [a] -> ExceptT SomeException IO ([String], EvaluationResultDef)
runPlcCekTrace values = do
     ps <- Haskell.traverse getProgram values
     let p = foldl1 applyProgram ps
     let (logOut, result) = evaluateCekTrace p
     res <- either (throwError . SomeException) Haskell.pure result
     Haskell.pure (logOut, res)

goldenEvalCek :: GetProgram a => String -> [a] -> TestNested
goldenEvalCek name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug Haskell.<$> (rethrow $ runPlcCek values)

goldenEvalCekLog :: GetProgram a => String -> [a] -> TestNested
goldenEvalCekLog name values = nestedGoldenVsDocM name $ (pretty . fst) Haskell.<$> (rethrow $ runPlcCekTrace values)

tests :: TestNested
tests = testNested "TH" [
    goldenPir "simple" simple
    , goldenPir "power" powerPlc
    , goldenPir "and" andPlc
    , goldenEvalCek "all" [allPlc]
    , goldenEvalCek "convertString" [convertString]
    , goldenEvalCekLog "traceDirect" [traceDirect]
    , goldenEvalCekLog "tracePrelude" [tracePrelude]
    , goldenEvalCekLog "traceRepeatedly" [traceRepeatedly]
    -- want to see the raw structure, so using Show
    , nestedGoldenVsDoc "someData" (pretty $ show someData)
  ]

simple :: CompiledCode (Bool -> Integer)
simple = $$(compile [|| \(x::Bool) -> if x then (1::Integer) else (2::Integer) ||])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: CompiledCode (Integer -> Integer)
powerPlc = $$(compile [|| $$(power (4::Integer)) ||])

andPlc :: CompiledCode Bool
andPlc = $$(compile [|| $$(andTH) True False ||])

allPlc :: CompiledCode Bool
allPlc = $$(compile [|| all (\(x::Integer) -> x > 5) [7, 6] ||])

convertString :: CompiledCode Builtins.String
convertString = $$(compile [|| toPlutusString "test" ||])

traceDirect :: CompiledCode ()
traceDirect = $$(compile [|| Builtins.trace (toPlutusString "test") ||])

tracePrelude :: CompiledCode Integer
tracePrelude = $$(compile [|| trace (toPlutusString "test") (1::Integer) ||])

traceRepeatedly :: CompiledCode Integer
traceRepeatedly = $$(compile
     [||
               let i1 = traceH "Making my first int" (1::Integer)
                   i2 = traceH "Making my second int" (2::Integer)
                   i3 = traceH "Adding them up" (i1 + i2)
              in i3
    ||])

data SomeType = One Integer | Two | Three ()

someData :: (Data, Data, Data)
someData = (toData (One 1), toData Two, toData (Three ()))

makeIsDataIndexed ''SomeType [('Two, 0), ('One, 1), ('Three, 2)]
