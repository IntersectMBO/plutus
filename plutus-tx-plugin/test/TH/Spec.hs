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
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TH.Spec (tests) where

import Test.Tasty.Extras

import Lib

import PlutusCore.Pretty

import PlutusTx
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Prelude
import PlutusTx.Show (show)

import Prelude qualified as Haskell

import TH.TestTH

data SomeType = One Integer | Two | Three ()

makeIsDataIndexed ''SomeType [('Two, 0), ('One, 1), ('Three, 2)]

someData :: (BuiltinData, BuiltinData, BuiltinData)
someData = (toBuiltinData (One 1), toBuiltinData Two, toBuiltinData (Three ()))

tests :: TestNested
tests = testNestedGhc "TH" [
    goldenPir "simple" simple
    , goldenPir "power" powerPlc
    , goldenPir "and" andPlc
    , goldenEvalCek "all" [allPlc]
    , goldenEvalCek "convertString" [convertString]
    , goldenEvalCekLog "traceDirect" [traceDirect]
    , goldenEvalCekLog "tracePrelude" [tracePrelude]
    , goldenEvalCekLog "traceRepeatedly" [traceRepeatedly]
    -- want to see the raw structure, so using Show
    , nestedGoldenVsDoc "someData" "" (pretty $ Haskell.show someData)
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

convertString :: CompiledCode Builtins.BuiltinString
convertString = $$(compile [|| "test" ||])

traceDirect :: CompiledCode ()
traceDirect = $$(compile [|| Builtins.trace "test" () ||])

tracePrelude :: CompiledCode Integer
tracePrelude = $$(compile [|| trace "test" (1::Integer) ||])

traceRepeatedly :: CompiledCode Integer
traceRepeatedly = $$(compile
     [||
          let i1 = trace "Making my first int" (1::Integer)
              i2 = trace "Making my second int" (2::Integer)
              i3 = trace ("Adding them up: " <> show (i1 + i2)) (i1 + i2)
          in i3
    ||])
