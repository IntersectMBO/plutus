-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Plugin.Errors.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Test ()

import Data.Proxy
import Data.String

-- Normally GHC will irritatingly case integers for us in some circumstances, but we want to do it
-- explicitly here, so we need to see the constructors.
import GHC.Num.Integer

-- this module does lots of weird stuff deliberately
{- HLINT ignore -}

errors :: TestNested
errors = testNestedGhc "Errors" [
    goldenUPlcCatch "machInt" machInt
    -- FIXME: This fails differently in nix, possibly due to slightly different optimization settings
    -- , goldenPlcCatch "negativeInt" negativeInt
    , goldenUPlcCatch "caseInt" caseInt
    , goldenUPlcCatch "stringLiteral" stringLiteral
    , goldenUPlcCatch "recursiveNewtype" recursiveNewtype
    , goldenUPlcCatch "mutualRecursionUnfoldingsLocal" mutualRecursionUnfoldingsLocal
    , goldenUPlcCatch "literalCaseInt" literalCaseInt
    , goldenUPlcCatch "literalCaseBs" literalCaseBs
    , goldenUPlcCatch "literalAppendBs" literalAppendBs
    , goldenUPlcCatch "literalCaseOther" literalCaseOther
  ]

machInt :: CompiledCode Int
machInt = plc (Proxy @"machInt") (1::Int)

negativeInt :: CompiledCode Integer
negativeInt = plc (Proxy @"negativeInt") (-1 :: Integer)

caseInt :: CompiledCode (Integer -> Bool)
caseInt = plc (Proxy @"caseInt") (\(i::Integer) -> case i of { IS _ -> True; _ -> False; } )

stringLiteral :: CompiledCode String
stringLiteral = plc (Proxy @"stringLiteral") ("hello"::String)

newtype RecursiveNewtype = RecursiveNewtype [RecursiveNewtype]

recursiveNewtype :: CompiledCode (RecursiveNewtype)
recursiveNewtype = plc (Proxy @"recursiveNewtype") (RecursiveNewtype [])

{-# INLINABLE evenDirectLocal #-}
evenDirectLocal :: Integer -> Bool
evenDirectLocal n = if Builtins.equalsInteger n 0 then True else oddDirectLocal (Builtins.subtractInteger n 1)

{-# INLINABLE oddDirectLocal #-}
oddDirectLocal :: Integer -> Bool
oddDirectLocal n = if Builtins.equalsInteger n 0 then False else evenDirectLocal (Builtins.subtractInteger n 1)

-- FIXME: these seem to only get unfoldings when they're in a separate module, even with the simplifier pass
mutualRecursionUnfoldingsLocal :: CompiledCode Bool
mutualRecursionUnfoldingsLocal = plc (Proxy @"mutualRecursionUnfoldingsLocal") (evenDirectLocal 4)

literalCaseInt :: CompiledCode (Integer -> Integer)
literalCaseInt = plc (Proxy @"literalCaseInt") (\case { 1 -> 2; x -> x})

literalCaseBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalCaseBs = plc (Proxy @"literalCaseBs") (\x -> case x of { "abc" -> ""; x -> x})

literalAppendBs :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
literalAppendBs = plc (Proxy @"literalAppendBs") (\x -> Builtins.appendByteString "hello" x)

data AType = AType

instance IsString AType where
    fromString _ = AType

instance Eq AType where
    AType == AType = True

literalCaseOther :: CompiledCode (AType -> AType)
literalCaseOther = plc (Proxy @"literalCaseOther") (\x -> case x of { "abc" -> ""; x -> x})
