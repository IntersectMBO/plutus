{-# LANGUAGE Strict, DataKinds, MultiParamTypeClasses, NoImplicitPrelude, ScopedTypeVariables, OverloadedStrings, TemplateHaskell, ViewPatterns #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas -fno-omit-interface-pragmas -fno-full-laziness -fno-spec-constr -fno-specialise -fno-strictness -fno-unbox-strict-fields -fno-unbox-small-strict-fields -fno-warn-missing-signatures -fno-warn-unused-matches #-}
-- for srcspans
{-# OPTIONS_GHC -g #-}
-- disable opts
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-pir #-}

module Main where

import PlutusTx.Code
import PlutusTx.Builtins as Tx
import PlutusTx as Tx
import PlutusTx.Prelude as Tx

-- EXAMPLE 1

ex1 :: CompiledCode Integer
ex1 = $$(compile [|| 1 ||])

-- EXAMPLE 2

ex2 :: CompiledCode (Integer -> Integer)
ex2 = $$(compile [|| \x -> Tx.addInteger x (Tx.addInteger 1 1) ||])

-- EXAMPLE 3

ex3 :: CompiledCode (BuiltinString -> BuiltinString)
ex3 = $$(compile [|| \s -> appendString "hello" s ||])

-- EXAMPLE 4

ex4 :: CompiledCode BuiltinString
ex4 = $$(compile [|| if True then "ok" else "5" ||])

-- EXAMPLE 5

type Datum = Integer
type Redeemer = Integer
type ScriptContext = () -- dummy
type Validator = Datum -> Redeemer -> ScriptContext -> Bool
type UntypedValidator = BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit

isEven, isOdd :: Integer -> Bool
isEven n = modInteger n 2 == 0
isOdd n = modInteger n 2 == 1

validator :: Validator
validator datum redeemer _ctx = isEven datum && isOdd redeemer && datum > redeemer

ex5 :: CompiledCode Validator
ex5 = $$(compile [|| validator ||])

fromTyped :: Validator -> UntypedValidator
fromTyped f =
    \(Tx.unsafeFromBuiltinData -> datum) (Tx.unsafeFromBuiltinData -> redeemer) (Tx.unsafeFromBuiltinData -> ctx) ->
        Tx.check (f datum redeemer ctx)

ex5FromTyped = $$(compile [|| fromTyped ||])

main = return ()
