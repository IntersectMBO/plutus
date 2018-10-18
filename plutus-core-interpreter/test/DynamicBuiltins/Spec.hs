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

typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Quote (Term TyName Name ()) -> m EvaluationResult
typecheckEvaluate meanings getTerm = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
    term <- liftQuote getTerm
    _ <- annotateTerm term >>= typecheckTerm (TypeCheckCfg 1000 $ TypeConfig True types)
    return $ evaluateCek meanings term

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning :: DynamicBuiltinNameMeaning
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch =
        TypeSchemeAllSize $ \s ->
            -- This argument is only for making the type signatures of the dynamic factorial and
            -- the defined in PLC factorial match. TODO: remove once @sizeOfInteger@ lands.
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)  `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)
    fac _size n = product [1..n]

dynamicFactorialDefinition :: DynamicBuiltinNameDefinition
dynamicFactorialDefinition = DynamicBuiltinNameDefinition dynamicFactorialName dynamicFactorialMeaning

dynamicFactorial :: Term tyname name ()
dynamicFactorial = Constant () $ DynBuiltinName () dynamicFactorialName

test_dynamicFactorial :: TestTree
test_dynamicFactorial = testCase "dynamicFactorial" $
        runQuoteT (typecheckEvaluate
            (insertDynamicBuiltinNameDefinition dynamicFactorialDefinition mempty)
            (pure $ applyFactorial dynamicFactorial 3 10))
    @?=
        Right (evaluateCek mempty $ applyFactorial (runQuote getBuiltinFactorial) 3 10)
