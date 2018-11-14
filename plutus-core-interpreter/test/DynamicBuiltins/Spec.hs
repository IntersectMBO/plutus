-- | Dynamic built-ins tests.

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Spec
    ( test_dynamicFactorial
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.Except
import           Test.Tasty
import           Test.Tasty.HUnit

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Quote (Term TyName Name ()) -> m EvaluationResult
typecheckEvaluate meanings getTerm = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
    term <- liftQuote getTerm
    _ <- annotateTerm term >>= typecheckTerm (TypeConfig True types (Just 1000))
    return $ evaluateCek meanings term

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning :: DynamicBuiltinNameMeaning
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch =
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)  `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)
    fac n = product [1..n]

dynamicFactorialDefinition :: DynamicBuiltinNameDefinition
dynamicFactorialDefinition = DynamicBuiltinNameDefinition dynamicFactorialName dynamicFactorialMeaning

dynamicFactorial :: Term tyname name ()
dynamicFactorial = dynamicBuiltinNameAsTerm dynamicFactorialName

-- | Check that the dynamic factorial defined above computes to the same thing as
-- a factorial defined in PLC itself.
test_dynamicFactorial :: TestTree
test_dynamicFactorial = testCase "dynamicFactorial" $
        runQuoteT (typecheckEvaluate
            (insertDynamicBuiltinNameDefinition dynamicFactorialDefinition mempty)
            (pure $ applyFactorial dynamicFactorial 3 10))
    @?=
        Right (evaluateCek mempty $ applyFactorial (runQuote getBuiltinFactorial) 3 10)
