{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Errors.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

import           Data.String

-- Normally GHC will irritatingly case integers for us in some circumstances, but we want to do it
-- explicitly here, so we need to see the constructors.
import           GHC.Integer.GMP.Internals

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

errors :: TestNested
errors = testNested "Errors" [
    goldenPlcCatch "machInt" machInt
    -- FIXME: This fails differently in nix, possibly due to slightly different optimization settings
    --, goldenPlcCatch "negativeInt" negativeInt
    , goldenPlcCatch "caseInt" caseInt
    , goldenPlcCatch "valueRestriction" valueRestriction
    , goldenPlcCatch "recursiveNewtype" recursiveNewtype
    , goldenPlcCatch "mutualRecursionUnfoldingsLocal" mutualRecursionUnfoldingsLocal
    , goldenPlcCatch "literalCaseInt" literalCaseInt
    , goldenPlcCatch "literalCaseBs" literalCaseBs
    , goldenPlcCatch "literalCaseOther" literalCaseOther
  ]

machInt :: CompiledCode Int
machInt = plc @"machInt" (1::Int)

negativeInt :: CompiledCode Integer
negativeInt = plc @"negativeInt" (-1 :: Integer)

caseInt :: CompiledCode (Integer -> Bool)
caseInt = plc @"caseInt" (\(i::Integer) -> case i of { S# i -> True; _ -> False; } )

-- It's little tricky to get something that GHC actually turns into a polymorphic computation! We use our value twice
-- at different types to prevent the obvious specialization.
valueRestriction :: CompiledCode (Bool, Integer)
valueRestriction = plc @"valueRestriction" (let { f :: forall a . a; f = Builtins.error (); } in (f @Bool, f @Integer))

newtype RecursiveNewtype = RecursiveNewtype [RecursiveNewtype]

recursiveNewtype :: CompiledCode (RecursiveNewtype)
recursiveNewtype = plc @"recursiveNewtype" (RecursiveNewtype [])

{-# INLINABLE evenDirectLocal #-}
evenDirectLocal :: Integer -> Bool
evenDirectLocal n = if Builtins.equalsInteger n 0 then True else oddDirectLocal (Builtins.subtractInteger n 1)

{-# INLINABLE oddDirectLocal #-}
oddDirectLocal :: Integer -> Bool
oddDirectLocal n = if Builtins.equalsInteger n 0 then False else evenDirectLocal (Builtins.subtractInteger n 1)

-- FIXME: these seem to only get unfoldings when they're in a separate module, even with the simplifier pass
mutualRecursionUnfoldingsLocal :: CompiledCode Bool
mutualRecursionUnfoldingsLocal = plc @"mutualRecursionUnfoldingsLocal" (evenDirectLocal 4)

literalCaseInt :: CompiledCode (Integer -> Integer)
literalCaseInt = plc @"literalCaseInt" (\case { 1 -> 2; x -> x})

literalCaseBs :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
literalCaseBs = plc @"literalCaseBs" (\x -> case x of { "abc" -> ""; x -> x})

data AType = AType

instance IsString AType where
    fromString _ = AType

instance Eq AType where
    AType == AType = True

-- Unfortunately, this actually succeeds, since the match gets turned into an equality and we can actually inline it.
-- I'm leaving it here since I'd really prefer it were an error for consistency, but I'm not sure how to do that nicely.
literalCaseOther :: CompiledCode (AType -> AType)
literalCaseOther = plc @"literalCaseOther" (\x -> case x of { "abc" -> ""; x -> x})
