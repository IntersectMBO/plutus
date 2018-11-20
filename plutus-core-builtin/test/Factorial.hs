-- | A dynamic built-in name test.

{-# LANGUAGE OverloadedStrings #-}

module Factorial
    ( test_dynamicFactorial
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.Interesting

import           Language.PlutusCore.Interpreter.CekMachine

import           Language.PlutusCore.Builtin

import           Test.Tasty
import           Test.Tasty.HUnit

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning :: DynamicBuiltinNameMeaning
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch =
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)
    fac n = product [1..n]

dynamicFactorialDefinition :: DynamicBuiltinNameDefinition
dynamicFactorialDefinition =
    DynamicBuiltinNameDefinition dynamicFactorialName dynamicFactorialMeaning

dynamicFactorial :: Term tyname name ()
dynamicFactorial = dynamicBuiltinNameAsTerm dynamicFactorialName

-- | Check that the dynamic factorial defined above computes to the same thing as
-- a factorial defined in PLC itself.
test_dynamicFactorial :: TestTree
test_dynamicFactorial = testCase "dynamicFactorial" $
        runQuoteT (typecheckEvaluate
            (insertDynamicBuiltinNameDefinition dynamicFactorialDefinition mempty)
            (applyFactorial dynamicFactorial 3 10))
    @?=
        Right (evaluateCek mempty $ applyFactorial (runQuote getBuiltinFactorial) 3 10)
