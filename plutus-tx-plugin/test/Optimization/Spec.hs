{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

{-# OPTIONS_GHC -fmax-simplifier-iterations=0 -fforce-recomp -O0 #-}

module Optimization.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Prelude qualified as P
import PlutusTx.Test (goldenPir)
import PlutusTx.TH (compile)

-- These are tests that run with the simplifier on, and run all the way to UPLC.
-- This can be interesting to make sure that important optimizations fire, including
-- ones that run on UPLC.
tests :: TestNested
tests = testNested "Optimization" [
    goldenUPlc "maybeFun" maybeFun
  , goldenUPlc "trueOrError" trueOrError
  , goldenPir "trueOrErrorPir" trueOrError
  , goldenUEval "trueOrErrorEval" [ toUPlc trueOrError ]
  , goldenUPlc "trueOrErrorOpaque" trueOrErrorOpaque
  , goldenPir "trueOrErrorOpaquePir" trueOrErrorOpaque
  , goldenUEval "trueOrErrorOpaqueEval" [ toUPlc trueOrErrorOpaque ]
  ]

-- The point of this test is to check that matchers get eliminated unconditionally
-- even if they're used more than once.
maybeFun :: CompiledCode (Maybe Integer -> Maybe Integer -> Maybe Integer)
maybeFun = $$(compile
   [|| \(x :: Maybe Integer) (y :: Maybe Integer) ->
         case x of
            Just x' -> case y of
                 Just y' -> Just (x' `PlutusTx.addInteger` y')
                 Nothing -> Nothing
            Nothing -> Nothing
   ||])

trueOrError :: CompiledCode Bool
trueOrError = $$(compile [|| c True (P.error () :: Bool) ||])
  where
    c x _ = x

trueOrErrorOpaque :: CompiledCode Bool
trueOrErrorOpaque = $$(compile [|| P.const True (P.error () :: Bool) ||])
