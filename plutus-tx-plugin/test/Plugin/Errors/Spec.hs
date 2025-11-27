-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Errors.Spec where

import Test.Tasty.Extras

import PlutusCore.Test (goldenUPlc)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode)
import PlutusTx.Plugin.Utils (plc)
import PlutusTx.Test ()

import Data.Proxy
import Data.String

-- Normally GHC will irritatingly case integers for us in some circumstances, but we want to do it
-- explicitly here, so we need to see the constructors.
import GHC.Num.Integer

-- this module does lots of weird stuff deliberately
{- HLINT ignore -}

errors :: TestNested
errors =
  testNested "Errors" . pure $
    testNestedGhc
      [ goldenUPlc "machInt" machInt
      , -- FIXME(https://github.com/IntersectMBO/plutus-private/issues/1608):
        -- This fails differently in nix, possibly due to slightly different optimization settings
        -- , goldenPlc "negativeInt" negativeInt
        goldenUPlc "caseInt" caseInt
      , goldenUPlc "stringLiteral" stringLiteral
      , goldenUPlc "recursiveNewtype" recursiveNewtype
      , goldenUPlc "mutualRecursionUnfoldingsLocal" mutualRecursionUnfoldingsLocal
      , goldenUPlc "literalCaseBs" literalCaseBs
      , goldenUPlc "literalAppendBs" literalAppendBs
      , goldenUPlc "literalCaseOther" literalCaseOther
      , goldenUPlc "rangeEnumFromTo" rangeEnumFromTo
      , goldenUPlc "rangeEnumFromThenTo" rangeEnumFromThenTo
      , goldenUPlc "rangeEnumFrom" rangeEnumFrom
      , goldenUPlc "rangeEnumFromThen" rangeEnumFromThen
      , goldenUPlc "toBuiltinUsed" toBuiltinUsed
      , goldenUPlc "fromBuiltinUsed" fromBuiltinUsed
      ]

machInt :: CompiledCode Int
machInt = plc (Proxy @"machInt") (1 :: Int)

negativeInt :: CompiledCode Integer
negativeInt = plc (Proxy @"negativeInt") (-1 :: Integer)

caseInt :: CompiledCode (Integer -> Bool)
caseInt = plc (Proxy @"caseInt") (\(i :: Integer) -> case i of IS _ -> True; _ -> False)

stringLiteral :: CompiledCode String
stringLiteral = plc (Proxy @"stringLiteral") ("hello" :: String)

newtype RecursiveNewtype = RecursiveNewtype [RecursiveNewtype]

recursiveNewtype :: CompiledCode (RecursiveNewtype)
recursiveNewtype = plc (Proxy @"recursiveNewtype") (RecursiveNewtype [])

evenDirectLocal :: Integer -> Bool
evenDirectLocal n = if Builtins.equalsInteger n 0 then True else oddDirectLocal (Builtins.subtractInteger n 1)
{-# INLINEABLE evenDirectLocal #-}

oddDirectLocal :: Integer -> Bool
oddDirectLocal n = if Builtins.equalsInteger n 0 then False else evenDirectLocal (Builtins.subtractInteger n 1)
{-# INLINEABLE oddDirectLocal #-}

-- FIXME: these seem to only get unfoldings when they're in a separate module, even with the simplifier pass
mutualRecursionUnfoldingsLocal :: CompiledCode Bool
mutualRecursionUnfoldingsLocal = plc (Proxy @"mutualRecursionUnfoldingsLocal") (evenDirectLocal 4)

literalCaseBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalCaseBs = plc (Proxy @"literalCaseBs") (\x -> case x of "abc" -> ""; x -> x)

literalAppendBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalAppendBs = plc (Proxy @"literalAppendBs") (\x -> Builtins.appendByteString "hello" x)

data AType = AType

instance IsString AType where
  fromString _ = AType

instance Eq AType where
  AType == AType = True

literalCaseOther :: CompiledCode (AType -> AType)
literalCaseOther = plc (Proxy @"literalCaseOther") (\x -> case x of "abc" -> ""; x -> x)

-- Tests for literal ranges (and the corresponding methods in GHC.Enum). These
-- should all fail with informative error messages.
rangeEnumFromTo :: CompiledCode [Integer]
rangeEnumFromTo = plc (Proxy @"rangeEnumFromTo") [1 .. 50]

rangeEnumFromThenTo :: CompiledCode [Integer]
rangeEnumFromThenTo = plc (Proxy @"rangeEnumFromThenTo") [1, 7 .. 50]

rangeEnumFrom :: CompiledCode [Integer]
rangeEnumFrom = plc (Proxy @"rangeEnumFrom") [1 ..]

rangeEnumFromThen :: CompiledCode [Integer]
rangeEnumFromThen = plc (Proxy @"rangeEnumFromThen") [1, 5 ..]

toBuiltinUsed :: CompiledCode (Integer -> Integer)
toBuiltinUsed = plc (Proxy @"toBuiltinUsed") Builtins.toBuiltin

fromBuiltinUsed :: CompiledCode (Integer -> Integer)
fromBuiltinUsed = plc (Proxy @"fromBuiltinUsed") Builtins.fromBuiltin
