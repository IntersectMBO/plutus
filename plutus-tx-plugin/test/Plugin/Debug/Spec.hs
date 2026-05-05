{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Debug.Spec where

import Test.Tasty.Extras

import Plinth.Plugin
import PlutusCore.Pretty
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Test

debug :: TestNested
debug =
  testNested "Debug" . pure $
    testNestedGhc
      [ goldenPirBy config "letFun" letFun
      , goldenPirBy config "fib" fib
      ]
  where
    config = PrettyConfigClassic prettyConfigNameSimple True

letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun =
  plinthc
    (\(x :: Integer) (y :: Integer) -> let f z = Builtins.equalsInteger x z in f y)

fib :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fib =
  plinthc
    ( let fib :: Integer -> Integer
          fib n =
            if Builtins.equalsInteger n 0
              then 0
              else
                if Builtins.equalsInteger n 1
                  then 1
                  else
                    Builtins.addInteger
                      (fib (Builtins.subtractInteger n 1))
                      (fib (Builtins.subtractInteger n 2))
       in fib
    )
