{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -g #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-pir #-}

module Main where

import Data.ByteString as BS
import Flat
import PlutusTx.Code
import PlutusTx.Builtins as Tx
import PlutusTx as Tx
import PlutusTx.Prelude as Tx

------------- EXAMPLE 1

ex1 :: CompiledCode Integer
ex1 = $$(compile [|| 1 ||])

------------- EXAMPLE 2

ex2 :: CompiledCode (Bool -> Bool -> Bool)
ex2 = $$(compile [|| \x y -> x ||])

------------- EXAMPLE 3

ex3 :: CompiledCode (BuiltinString -> BuiltinString)
ex3 = $$(compile [|| \s -> appendString "hello" s ||])

------------- EXAMPLE 4

-- ill-typed, check uplc, also ghc may optimise this away
-- ex4 = $$(compile [|| if True then "ok" else "5" ||])

------------- EXAMPLE 5


isEven :: Integer -> Bool
isEven n = modInteger n 2 == 0

isOdd :: Integer -> Bool
isOdd n = modInteger n 2 == 1


ex5 :: Integer -> Integer -> ScriptContext -> Bool
ex5 = \datum redeemer _ctx ->
          isEven datum && isOdd redeemer && datum > redeemer
type ScriptContext = () -- dummy

ex5Typed :: CompiledCode (Integer -> Integer -> ScriptContext -> Bool)
ex5Typed = $$(compile [|| ex5 ||])

fromTyped :: (Integer -> Integer -> ScriptContext -> Bool)
          -> (BuiltinData -> BuiltinData -> BuiltinData -> ())
fromTyped f =
    \(Tx.unsafeFromBuiltinData -> datum) (Tx.unsafeFromBuiltinData -> redeemer) (Tx.unsafeFromBuiltinData -> ctx) ->
        Tx.check (f datum redeemer ctx)

ex5FromTyped = $$(compile [|| fromTyped ||])

main = return ()
