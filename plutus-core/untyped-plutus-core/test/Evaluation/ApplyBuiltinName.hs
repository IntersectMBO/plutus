{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyDefaultBuiltin
    ) where

import           UntypedPlutusCore

import           PlutusCore.Builtins
import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Generators
import           PlutusCore.Universe

import           Control.Monad.Except
import           Data.Proxy
import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- | A simplified (because we don't need the full generality here) CPS-transformed
-- (so that we can provide the 'KnownType' constraint to the caller) version of
-- 'PlutusCore.Generators.Internal.Entity.genIterAppValue'.
withGenArgsRes
    :: (Generatable uni, Monad m)
    => TypeScheme (Term Name uni fun ()) as res
    -> FoldArgs as res
    -> (KnownType (Term Name uni fun ()) res => [Term Name uni fun ()] -> res -> PropertyT m r)
    -> PropertyT m r
withGenArgsRes (TypeSchemeResult _)     y k = k [] y
withGenArgsRes (TypeSchemeArrow _ schB) f k = do
    TermOf v x <- forAllNoShow $ genTypedBuiltinDef AsKnownType
    withGenArgsRes schB (f x) (k . (v :))
withGenArgsRes (TypeSchemeAll _ schK)   f k = withGenArgsRes (schK Proxy) f k

type AppErr =
    EvaluationException
        ()
        (MachineError DefaultFun (Term Name DefaultUni DefaultFun ()))
        (Term Name DefaultUni DefaultFun ())

-- | A simple monad for evaluating constant applications in.
newtype AppM a = AppM
    { unAppM :: Either AppErr a
    } deriving newtype (Functor, Applicative, Monad, MonadError AppErr)
      deriving (MonadEmitter) via (NoEmitterT AppM)

instance SpendBudget AppM DefaultFun () where
    spendBudget _ _ = pure ()

-- | This shows that the builtin application machinery accepts untyped terms.
test_applyBuiltinFunction :: DefaultFun -> TestTree
test_applyBuiltinFunction fun =
    testProperty (show fun) . property $ case toBuiltinMeaning fun of
        BuiltinMeaning sch f toExF -> do
            let exF = toExF defaultBuiltinCostModel
            withGenArgsRes sch f $ \args res ->
                -- The calls to 'unAppM' are just to drive type inference.
                unAppM (applyTypeSchemed fun sch f exF args) === unAppM (makeKnown res)

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
