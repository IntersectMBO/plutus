{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Debug.Spec where

import Test.Tasty.Extras

import PlutusCore.Pretty
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Test

import Data.Proxy

debug :: TestNested
debug =
    testNestedGhc
        "Debug"
        [ goldenPirBy config "letFun" letFun
        , goldenPirBy config "fib" fib
        ]
  where
    config = PrettyConfigClassic defPrettyConfigName True

letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun =
    plc
        (Proxy @"letFun")
        (\(x :: Integer) (y :: Integer) -> let f z = Builtins.equalsInteger x z in f y)

fib :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fib =
    plc
        (Proxy @"fib")
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
