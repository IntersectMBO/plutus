{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC   -g #-}

module TH.Spec (tests) where

import           Common
import           PlcTestUtils
import           PlutusPrelude                (view)

import           TH.TestTH

import qualified Prelude                      as Haskell

import           Language.PlutusTx
import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Evaluation
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.TH

import qualified Language.PlutusIR            as PIR

import           Language.PlutusCore
import           Language.PlutusCore.Pretty
import qualified Language.PlutusCore.Universe as PLC

import           Control.Exception
import           Control.Lens.Combinators     (_1)
import           Control.Monad.Except

import           Data.Text.Prettyprint.Doc
import           Test.Tasty

instance uni ~ PLC.DefaultUni => GetProgram (CompiledCode uni a) uni where
    getProgram = catchAll . getPlc

goldenPir :: String -> CompiledCode PLC.DefaultUni a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value

runPlcCek :: GetProgram a PLC.DefaultUni => [a] -> ExceptT SomeException IO (Plain Term PLC.DefaultUni)
runPlcCek values = do
     ps <- Haskell.traverse getProgram values
     let p = foldl1 applyProgram ps
     either (throwError . SomeException) Haskell.pure $ evaluateCek p

runPlcCekTrace :: GetProgram a PLC.DefaultUni => [a] -> ExceptT SomeException IO ([String], ExTally, (Plain Term PLC.DefaultUni))
runPlcCekTrace values = do
     ps <- Haskell.traverse getProgram values
     let p = foldl1 applyProgram ps
     let (logOut, tally, result) = evaluateCekTrace p
     res <- either (throwError . SomeException) Haskell.pure result
     Haskell.pure (logOut, tally, res)

goldenEvalCek :: GetProgram a PLC.DefaultUni => String -> [a] -> TestNested
goldenEvalCek name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug Haskell.<$> (rethrow $ runPlcCek values)

goldenEvalCekLog :: GetProgram a PLC.DefaultUni => String -> [a] -> TestNested
goldenEvalCekLog name values = nestedGoldenVsDocM name $ (pretty . (view _1)) Haskell.<$> (rethrow $ runPlcCekTrace values)

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

simple :: CompiledCode PLC.DefaultUni (Bool -> Integer)
simple = $$(compile [|| \(x::Bool) -> if x then (1::Integer) else (2::Integer) ||])

-- similar to the power example for Feldspar - should be completely unrolled at compile time
powerPlc :: CompiledCode PLC.DefaultUni (Integer -> Integer)
powerPlc = $$(compile [|| $$(power (4::Integer)) ||])

andPlc :: CompiledCode PLC.DefaultUni Bool
andPlc = $$(compile [|| $$(andTH) True False ||])

allPlc :: CompiledCode PLC.DefaultUni Bool
allPlc = $$(compile [|| all (\(x::Integer) -> x > 5) [7, 6] ||])

convertString :: CompiledCode PLC.DefaultUni Builtins.String
convertString = $$(compile [|| "test" ||])

traceDirect :: CompiledCode PLC.DefaultUni ()
traceDirect = $$(compile [|| Builtins.trace "test" ||])

tracePrelude :: CompiledCode PLC.DefaultUni Integer
tracePrelude = $$(compile [|| trace "test" (1::Integer) ||])

traceRepeatedly :: CompiledCode PLC.DefaultUni Integer
traceRepeatedly = $$(compile
     [||
               let i1 = trace "Making my first int" (1::Integer)
                   i2 = trace "Making my second int" (2::Integer)
                   i3 = trace "Adding them up" (i1 + i2)
              in i3
    ||])

data SomeType = One Integer | Two | Three ()

someData :: (Data, Data, Data)
someData = (toData (One 1), toData Two, toData (Three ()))

makeIsDataIndexed ''SomeType [('Two, 0), ('One, 1), ('Three, 2)]
