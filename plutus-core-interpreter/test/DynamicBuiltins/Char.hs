{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Char (test_putChar) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Data.Char
import           Data.Maybe
import           System.IO.Unsafe

instance KnownDynamicBuiltinType Char where
    dynamicBuiltinType = TypedDynamicBuiltinType $ DynamicBuiltinType "char"

    makeDynamicBuiltin = fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _                                   = Nothing

dynamicIntegerToCharName :: DynamicBuiltinName
dynamicIntegerToCharName = DynamicBuiltinName "integerToChar"

dynamicIntegerToCharDefinition :: DynamicBuiltinNameDefinition
dynamicIntegerToCharDefinition =
    DynamicBuiltinNameDefinition dynamicIntegerToCharName $ DynamicBuiltinNameMeaning sch sem where
        sch :: TypeScheme size (Integer -> Char) Char
        sch =
            TypeSchemeAllSize $ \s ->
                TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
                TypeSchemeBuiltin TypedBuiltinDyn
        sem = chr . fromIntegral

dynamicIntegerToChar :: Term tyname name ()
dynamicIntegerToChar = dynamicBuiltinNameAsTerm dynamicIntegerToCharName

dynamicPutCharName :: DynamicBuiltinName
dynamicPutCharName = DynamicBuiltinName "putChar"

dynamicPutCharDefinition :: DynamicBuiltinNameDefinition
dynamicPutCharDefinition =
    DynamicBuiltinNameDefinition dynamicPutCharName $ DynamicBuiltinNameMeaning sch sem where
        sch :: TypeScheme size (Char -> ()) ()
        sch =
            TypeSchemeBuiltin TypedBuiltinDyn `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . print

dynamicPutChar :: Term tyname name ()
dynamicPutChar = dynamicBuiltinNameAsTerm dynamicPutCharName

charToTerm :: Char -> Term TyName Name ()
charToTerm = fromMaybe (error "'charToTerm': failed") . makeDynamicBuiltin

examplePutChar :: Term TyName Name ()
examplePutChar = Apply () dynamicPutChar $ charToTerm 'a'

test_putChar :: EvaluationResult
test_putChar = evaluateCek mempty examplePutChar
