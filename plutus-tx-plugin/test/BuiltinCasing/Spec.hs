{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

{-| This module tests compilation of built-in types into UPLC's casing of constants
the examples also appear in the Plinth guide page about case -}
module BuiltinCasing.Spec where

import Test.Tasty.Extras

import PlutusTx (compile)
import PlutusTx.Builtins (caseInteger, caseList, casePair)
import PlutusTx.Builtins.Internal (chooseUnit)
import PlutusTx.Prelude
import PlutusTx.Test

assert :: Bool -> ()
assert False = error ()
assert True = ()

forceUnit :: BuiltinUnit -> Integer
forceUnit e = chooseUnit e 5

addPair :: BuiltinPair Integer Integer -> Integer
addPair p = casePair p (+)

integerABC :: Integer -> BuiltinString
integerABC i = caseInteger i ["a", "b", "c"]

head :: BuiltinList Bool -> Bool
head xs = caseList (\_ -> error ()) (\x _ -> x) xs

tests :: TestNested
tests =
  testNested "BuiltinCasing"
    . pure
    $ testNestedGhc
      [ goldenUPlcReadable "assert" $$(compile [||assert||])
      , goldenUPlcReadable "forceUnit" $$(compile [||forceUnit||])
      , goldenUPlcReadable "addPair" $$(compile [||addPair||])
      , goldenUPlcReadable "integerABC" $$(compile [||integerABC||])
      , goldenUPlcReadable "head" $$(compile [||head||])
      ]
