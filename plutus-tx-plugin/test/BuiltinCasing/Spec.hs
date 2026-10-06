{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-| This module tests compilation of built-in types into UPLC's casing of constants
the examples also appear in the Plinth guide page about case -}
module BuiltinCasing.Spec where

import Test.Tasty.Extras

import BuiltinCasing.WithGHCOptimisations
import PlutusTx (compile)
import PlutusTx.Builtins (caseData, caseInteger, caseList, casePair, mkConstr)
import PlutusTx.Builtins.Internal (chooseUnit, unitval)
import PlutusTx.Prelude
import PlutusTx.Test

assert :: Bool -> BuiltinUnit
assert False = error ()
assert True = unitval

forceUnit :: BuiltinUnit -> Integer
forceUnit e = chooseUnit e 5

addPair :: BuiltinPair Integer Integer -> Integer
addPair p = casePair p (+)

integerABC :: Integer -> BuiltinString
integerABC i = caseInteger i ["a", "b", "c"]

head :: BuiltinList Bool -> Bool
head xs = caseList (\_ -> error ()) (\x _ -> x) xs

dataFields :: BuiltinData -> BuiltinList BuiltinData
dataFields d = caseData d [\xs -> xs]

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
      , goldenUPlcReadable "dataFields" $$(compile [||dataFields||])
      , assertResult
          "floatedIntegerBranches"
          $$( compile
                [||
                (selectIntegerBranch 0 == 10)
                  && (selectIntegerBranch 1 == 20)
                  && (selectIntegerBranch 2 == 30)
                ||]
            )
      , assertResult
          "floatedDataBranches"
          $$( compile
                [||
                (selectDataBranch (mkConstr 0 []) == 10)
                  && (selectDataBranch (mkConstr 1 []) == 20)
                  && (selectDataBranch (mkConstr 2 []) == 30)
                ||]
            )
      ]
