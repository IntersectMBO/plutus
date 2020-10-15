-- | Constant application tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyStaticBuiltin
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModel)
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Generators

import           Control.Monad.Except
import           Hedgehog                                                   hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- A monad to keep 'applyTypeSchemed' happy.
-- We can't use CekM or CkM because their exception types don't match 'Term'.
type AppErr = EvaluationException () () DefaultFun (Term TyName Name DefaultUni DefaultFun ())

-- | A simple monad for evaluating constant applications in.
newtype AppM a = AppM
    { unAppM :: Either AppErr a
    } deriving newtype (Functor, Applicative, Monad, MonadError AppErr)

instance SpendBudget AppM DefaultFun () (Term TyName Name DefaultUni DefaultFun ()) where
    spendBudget _ _ = pure ()

test_applyBuiltinFunction :: DefaultFun -> TestTree
test_applyBuiltinFunction fun =
    testProperty (show fun) . property $ case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> do
            let f = toF mempty
                exF = toExF defaultCostModel
                denot = Denotation fun (Builtin ()) f sch
                getIterAppValue = runPlcT genTypedBuiltinDef $ genIterAppValue denot
            IterAppValue _ iterApp res <- forAllNoShow getIterAppValue
            let IterApp _ args = iterApp
                rhs = makeKnown res
            case unAppM $ applyTypeSchemed fun sch f exF args of
                Left _    -> fail $ "Failure while checking an application of " ++ show fun
                Right lhs -> lhs === rhs

test_applyStaticBuiltin :: TestTree
test_applyStaticBuiltin =
    testGroup "applyStaticBuiltin"
        [ test_applyBuiltinFunction AddInteger
        , test_applyBuiltinFunction SubtractInteger
        , test_applyBuiltinFunction MultiplyInteger
        , test_applyBuiltinFunction DivideInteger
        , test_applyBuiltinFunction QuotientInteger
        , test_applyBuiltinFunction ModInteger
        , test_applyBuiltinFunction RemainderInteger
        , test_applyBuiltinFunction LessThanInteger
        , test_applyBuiltinFunction LessThanEqInteger
        , test_applyBuiltinFunction GreaterThanInteger
        , test_applyBuiltinFunction GreaterThanEqInteger
        , test_applyBuiltinFunction EqInteger
        , test_applyBuiltinFunction Concatenate
        , test_applyBuiltinFunction TakeByteString
        , test_applyBuiltinFunction DropByteString
        , test_applyBuiltinFunction EqByteString
        , test_applyBuiltinFunction SHA2
        , test_applyBuiltinFunction SHA3
        ]
