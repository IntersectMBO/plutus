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

module Optimization.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Test ()
import PlutusTx.TH (compile)

-- These are tests that run with the simplifier on, and run all the way to UPLC.
-- This can be interesting to make sure that important optimizations fire, including
-- ones that run on UPLC.
tests :: TestNested
tests = testNestedGhc "Optimization" [
   goldenUPlc "maybeFun" maybeFun ]

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
