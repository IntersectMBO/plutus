-- | Constant application tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyDefaultBuiltin
    ) where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel)
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Generators

import           Control.Monad.Except
import           Hedgehog                                          hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- A monad to keep 'applyTypeSchemed' happy.
-- We can't use CekM or CkM because their exception types don't match 'Term'.
type AppErr =
    EvaluationException
        ()
        (MachineError DefaultFun)
        (Term TyName Name DefaultUni DefaultFun ())

-- | A simple monad for evaluating constant applications in.
newtype AppM a = AppM
    { unAppM :: Either AppErr a
    } deriving newtype (Functor, Applicative, Monad, MonadError AppErr)
      deriving (MonadEmitter) via (NoEmitterT AppM)

test_applyBuiltinFunction :: DefaultFun -> TestTree
test_applyBuiltinFunction fun =
    testProperty (show fun) . property $ case toBuiltinMeaning fun of
        BuiltinMeaning sch f toExF -> do
            let exF = toExF defaultBuiltinCostModel
                denot = Denotation fun (Builtin ()) f sch
                getIterAppValue = runPlcT genTypedBuiltinDef $ genIterAppValue denot
            IterAppValue _ (IterApp _ args) res <- forAllNoShow getIterAppValue
            -- The calls to 'unAppM' are just to drive type inference.
            unAppM (applyTypeSchemed (\_ _ -> pure ()) fun sch f exF args) === unAppM (makeKnown res)

test_applyDefaultBuiltin :: TestTree
test_applyDefaultBuiltin =
    testGroup "applyDefaultBuiltin"
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
