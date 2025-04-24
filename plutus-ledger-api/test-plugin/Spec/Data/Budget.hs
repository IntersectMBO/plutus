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

module Spec.Data.Budget where

import Test.Tasty (TestName, TestTree)
import Test.Tasty.Extras

import Data.Bifunctor
import Data.String
import PlutusLedgerApi.V1.Data.Value
import PlutusTx.Code
import PlutusTx.Data.AssocMap as Map
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestTree
tests =
  runTestNested ["test-plugin", "Spec", "Data", "Budget"] . pure . testNestedGhc $
      [ goldenPirReadable "gt" compiledGt
      , goldenPirReadable "currencySymbolValueOf" compiledCurrencySymbolValueOf
      , goldenBundleBinOpApply "gt1" compiledGt value1 value1
      , goldenBundleBinOpApply "gt2" compiledGt value1 value2
      , goldenBundleBinOpApply "gt3" compiledGt value2 value1
      , goldenBundleBinOpApply "gt4" compiledGt value1 value3
      , goldenBundleBinOpApply "gt5" compiledGt value3 value1
      , goldenBundleBinOpApply "geq1" compiledGeq value1 value1
      , goldenBundleBinOpApply "geq2" compiledGeq value1 value2
      , goldenBundleBinOpApply "geq3" compiledGeq value2 value1
      , goldenBundleBinOpApply "geq4" compiledGeq value1 value3
      , goldenBundleBinOpApply "geq5" compiledGeq value3 value1
      -- , goldenBundleBinOpApply "currencySymbolValueOf"
            compiledCurrencySymbolValueOf value2 (toSymbol 6)
      ]


-- goldenBundleBinOpApply
  -- :: TestName -> CompiledCode (Value -> Value -> Bool) -> Value -> Value -> TestNested
goldenBundleBinOpApply name f x y =
  goldenBundle name f (f `unsafeApplyCode` liftCodeDef x `unsafeApplyCode` liftCodeDef y)


compiledGt :: CompiledCode (Value -> Value -> Bool)
compiledGt = $$(compile [||gt||])

compiledGeq :: CompiledCode (Value -> Value -> Bool)
compiledGeq = $$(compile [||geq||])

compiledCurrencySymbolValueOf :: CompiledCode (Value -> CurrencySymbol -> Integer)
compiledCurrencySymbolValueOf = $$(compile [||currencySymbolValueOf||])

mkValue :: [(Integer, [(Integer, Integer)])] -> Value
mkValue =
    Value
    . Map.unsafeFromSOPList
    . fmap (bimap toSymbol (Map.unsafeFromSOPList . fmap (first toToken)))

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
