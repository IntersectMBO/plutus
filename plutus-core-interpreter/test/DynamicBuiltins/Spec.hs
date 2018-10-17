{-# LANGUAGE FlexibleContexts #-}

module DynamicBuiltins.Spec where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Interpreter.CekMachine
-- import           Language.PlutusCore.Pretty
-- import           Language.PlutusCore.StdLib.Everything

-- import           Common

import           Control.Monad.Except
-- import           Test.Tasty
-- import           Test.Tasty.HUnit

typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Quote (Term TyName Name ()) -> m EvaluationResult
typecheckEvaluate meanings getTerm = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
    term <- liftQuote getTerm
    _ <- annotateTerm term >>= typecheckTerm (TypeCheckCfg 1000 $ TypeConfig True types)
    return $ evaluateCek meanings term

factorialMeaning :: DynamicBuiltinNameMeaning
factorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch =
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)
    fac n = product [1..n]

-- getBuiltinFactorial :: Quote (Term TyName Name ())
-- getBuiltinFactorial = undefined
