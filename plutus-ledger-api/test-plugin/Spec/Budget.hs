{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Spec.Budget where

import Test.Tasty (TestTree)
import Test.Tasty.Extras

import Data.Bifunctor
import Data.String
import PlutusLedgerApi.V1.Value
import PlutusTx.AssocMap as Map
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteString)
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test

tests :: TestTree
tests =
  runTestNested ["test-plugin", "Spec", "Budget"] . pure . testNestedGhc $
    [ goldenPirReadable "gt" compiledGt
    , goldenPirReadable "currencySymbolValueOf" compiledCurrencySymbolValueOf
    ]
      ++ testCases

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
toToken = TokenName . stringToBuiltinByteString . show

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

testCases :: [TestNested]
testCases =
  [ goldenEvalCekCatchBudget
      "gt1"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "gt2"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value2
      )
  , goldenEvalCekCatchBudget
      "gt3"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "gt4"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value3
      )
  , goldenEvalCekCatchBudget
      "gt5"
      ( compiledGt
          `unsafeApplyCode` liftCodeDef value3
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "geq1"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "geq2"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value2
      )
  , goldenEvalCekCatchBudget
      "geq3"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "geq4"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value1
          `unsafeApplyCode` liftCodeDef value3
      )
  , goldenEvalCekCatchBudget
      "geq5"
      ( compiledGeq
          `unsafeApplyCode` liftCodeDef value3
          `unsafeApplyCode` liftCodeDef value1
      )
  , goldenEvalCekCatchBudget
      "currencySymbolValueOf"
      ( compiledCurrencySymbolValueOf
          `unsafeApplyCode` liftCodeDef value2
          `unsafeApplyCode` liftCodeDef (toSymbol 6)
      )
  ]
