{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Spec.Budget where

import Test.Tasty (TestName, TestTree)
import Test.Tasty.Extras

import Data.Bifunctor
import Data.String
import Data.Traversable (for)
import PlutusLedgerApi.V1.Value
import PlutusTx.AssocMap as Map
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestTree
tests =
  runTestNestedIn ["test-plugin", "Spec"] . testNestedGhcM "Budget" $ do
    goldenPirReadable "gt" compiledGt
    goldenPirReadable "currencySymbolValueOf" compiledCurrencySymbolValueOf
    for testCases $  \(TestCase name code) -> do
      goldenBudget name code
      goldenEvalCekCatch name [code]

compiledGt :: CompiledCode (Value -> Value -> Bool)
compiledGt = $$(compile [||gt||])

compiledGeq :: CompiledCode (Value -> Value -> Bool)
compiledGeq = $$(compile [||geq||])

compiledCurrencySymbolValueOf :: CompiledCode (Value -> CurrencySymbol -> Integer)
compiledCurrencySymbolValueOf = $$(compile [||currencySymbolValueOf||])

mkValue :: [(Integer, [(Integer, Integer)])] -> Value
mkValue =
    Value . Map.unsafeFromList . fmap (bimap toSymbol (Map.unsafeFromList . fmap (first toToken)))

toSymbol :: Integer -> CurrencySymbol
toSymbol = currencySymbol . fromString . show

toToken :: Integer -> TokenName
toToken = fromString . show

value1 :: Value
value1 =
  mkValue
    [ (1, [(100, 101)])
    , (2, [(200, 201), (202, 203)])
    , (3, [(300, 301), (302, 303), (304, 305)])
    , (4, [(400, 401), (402, 403), (404, 405), (406, 407)])
    , (5, [(500, 501), (502, 503), (504, 505), (506, 507), (508, 509)])
    ]

-- | One more CurrencySymbol than `value1`.
value2 :: Value
value2 =
  mkValue
    [ (1, [(100, 101)])
    , (2, [(200, 201), (202, 203)])
    , (3, [(300, 301), (302, 303), (304, 305)])
    , (4, [(400, 401), (402, 403), (404, 405), (406, 407)])
    , (5, [(500, 501), (502, 503), (504, 505), (506, 507), (508, 509)])
    , (6, [(600, 601), (602, 603), (604, 605), (606, 607), (608, 609), (610, 611)])
    ]

-- | One more TokenName than `value1`.
value3 :: Value
value3 =
  mkValue
    [ (1, [(100, 101)])
    , (2, [(200, 201), (202, 203)])
    , (3, [(300, 301), (302, 303), (304, 305), (306, 307)])
    , (4, [(400, 401), (402, 403), (404, 405), (406, 407)])
    , (5, [(500, 501), (502, 503), (504, 505), (506, 507), (508, 509)])
    ]

data TestCase = forall a. TestCase TestName (CompiledCode a)

testCases :: [TestCase]
testCases =
  [ TestCase
      "gt1"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "gt2"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value2
      )
  , TestCase
      "gt3"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "gt4"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value3
      )
  , TestCase
      "gt5"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value3
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "geq1"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "geq2"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value2
      )
  , TestCase
      "geq3"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "geq4"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value3
      )
  , TestCase
      "geq5"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value3
          `unsafeApplyCode` liftCodeDef value1
      )
  , TestCase
      "currencySymbolValueOf"
      ( compiledCurrencySymbolValueOf
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef (toSymbol 6)
      )
  ]
