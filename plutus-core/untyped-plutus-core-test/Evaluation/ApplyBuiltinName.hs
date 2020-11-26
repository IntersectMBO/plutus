{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyStaticBuiltin
    ) where

import           Language.UntypedPlutusCore

import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import           Data.Proxy
import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- | A simplified (because we don't need the full generality here) CPS-transformed
-- (so that we can provide the 'KnownType' constraint to the caller) version of
-- 'Language.PlutusCore.Generators.Internal.Entity.genIterAppValue'.
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
withGenArgsRes (TypeSchemeAll _ _ schK) f k = withGenArgsRes (schK Proxy) f k

type AppErr = EvaluationException () DefaultFun (Term Name DefaultUni DefaultFun ())

-- | A simple monad for evaluating constant applications in.
newtype AppM a = AppM
    { unAppM :: Either AppErr a
    } deriving newtype (Functor, Applicative, Monad, MonadError AppErr)

instance SpendBudget AppM DefaultFun () (Term Name DefaultUni DefaultFun ()) where
    spendBudget _ _ = pure ()

-- | This shows that the builtin application machinery accepts untyped terms.
test_applyBuiltinFunction :: DefaultFun -> TestTree
test_applyBuiltinFunction fun =
    testProperty (show fun) . property $ case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> do
            let f = toF defDefaultFunDyn
                exF = toExF defaultCostModel
            withGenArgsRes sch f $ \args res ->
                -- The calls to 'unAppM' are just to drive type inference.
                unAppM (applyTypeSchemed fun sch f exF args) === unAppM (makeKnown res)

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
