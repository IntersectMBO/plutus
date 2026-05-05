-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Errors.Spec where

import Test.Tasty.Extras

import PlutusCore.Test (goldenUPlc)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode)
import PlutusTx.Plugin.Utils (plinthc)
import PlutusTx.Test ()

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
machInt = plinthc (1 :: Int)

negativeInt :: CompiledCode Integer
negativeInt = plinthc (-1 :: Integer)

caseInt :: CompiledCode (Integer -> Bool)
caseInt = plinthc (\(i :: Integer) -> case i of IS _ -> True; _ -> False)

stringLiteral :: CompiledCode String
stringLiteral = plinthc ("hello" :: String)

newtype RecursiveNewtype = RecursiveNewtype [RecursiveNewtype]

recursiveNewtype :: CompiledCode (RecursiveNewtype)
recursiveNewtype = plinthc (RecursiveNewtype [])

evenDirectLocal :: Integer -> Bool
evenDirectLocal n = if Builtins.equalsInteger n 0 then True else oddDirectLocal (Builtins.subtractInteger n 1)
{-# INLINEABLE evenDirectLocal #-}

oddDirectLocal :: Integer -> Bool
oddDirectLocal n = if Builtins.equalsInteger n 0 then False else evenDirectLocal (Builtins.subtractInteger n 1)
{-# INLINEABLE oddDirectLocal #-}

-- FIXME: these seem to only get unfoldings when they're in a separate module, even with the simplifier pass
mutualRecursionUnfoldingsLocal :: CompiledCode Bool
mutualRecursionUnfoldingsLocal = plinthc (evenDirectLocal 4)

literalCaseBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalCaseBs = plinthc (\x -> case x of "abc" -> ""; x -> x)

literalAppendBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalAppendBs = plinthc (\x -> Builtins.appendByteString "hello" x)

data AType = AType

instance IsString AType where
  fromString _ = AType

instance Eq AType where
  AType == AType = True

literalCaseOther :: CompiledCode (AType -> AType)
literalCaseOther = plinthc (\x -> case x of "abc" -> ""; x -> x)

-- Tests for literal ranges (and the corresponding methods in GHC.Enum). These
-- should all fail with informative error messages.
rangeEnumFromTo :: CompiledCode [Integer]
rangeEnumFromTo = plinthc [1 .. 50]

rangeEnumFromThenTo :: CompiledCode [Integer]
rangeEnumFromThenTo = plinthc [1, 7 .. 50]

rangeEnumFrom :: CompiledCode [Integer]
rangeEnumFrom = plinthc [1 ..]

rangeEnumFromThen :: CompiledCode [Integer]
rangeEnumFromThen = plinthc [1, 5 ..]

toBuiltinUsed :: CompiledCode (Integer -> Integer)
toBuiltinUsed = plinthc Builtins.toBuiltin

fromBuiltinUsed :: CompiledCode (Integer -> Integer)
fromBuiltinUsed = plinthc Builtins.fromBuiltin
