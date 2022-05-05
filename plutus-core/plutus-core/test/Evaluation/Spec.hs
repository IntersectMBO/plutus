{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Evaluation.Spec (test_evaluation) where

import PlutusCore hiding (Term)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Generators (SomeGen (..), forAllNoShow, genConstant)
import PlutusCore.Generators.AST hiding (genConstant)
import PlutusCore.Pretty

import Control.Exception
import Control.Monad.Except
import Control.Monad.Extra
import Data.Functor (($>))
import Data.Kind qualified as GHC
import Data.List.Extra qualified as List
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection

type Term fun = PLC.Term TyName Name DefaultUni fun ()

test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
    testGroup
        "Builtins don't throw"
        $ fmap
            (\fun -> testProperty (display fun) $ prop_builtinsDon'tThrow @DefaultFun fun)
            List.enumerate

{- | Evaluating a builtin function should never throw any exception (the evaluation is allowed
 to fail with a `KnownTypeError`, of course).

 The test covers both succeeding and failing evaluations and verifies that in either case
 no exception is thrown. The failing cases use arbitrary `Term` arguments (which doesn't
 guarantee failure, but most likely), and the succeeding cases generate `Term` arguments
 based on a builtin function's `TypeScheme`. For `Opaque` arguments it generates arbitrary
 `Term`s (which technically doesn't guarantee evaluation success, although it is the case
 with all current builtin functions).
-}
prop_builtinsDon'tThrow ::
    forall fun.
    (ToBuiltinMeaning DefaultUni fun, Pretty fun) =>
    fun ->
    Property
prop_builtinsDon'tThrow bn = property $ do
    args <- forAllNoShow . Gen.choice $ [genArgsWellTyped bn, genArgsArbitrary bn]
    mbErr <-
        liftIO $
            catch
                (($> Nothing) . evaluate . runEmitter . runExceptT $ eval args)
                (pure . pure)
    whenJust mbErr $ \(e :: SomeException) -> do
        annotate "Builtin function evaluation failed"
        annotate $ "Function: " <> display bn
        annotate $ "Arguments: " <> display args
        annotate $ "Error " <> show e
        failure
  where
    meaning :: BuiltinMeaning (Term fun) (CostingPart DefaultUni fun)
    meaning = toBuiltinMeaning bn

    eval :: [Term fun] -> MakeKnownM (Term fun)
    eval args0 = case meaning of
        BuiltinMeaning _ _ runtime -> go (_broRuntimeScheme runtime) (_broImmediateF runtime) args0
      where
        go ::
            forall n.
            RuntimeScheme n ->
            ToRuntimeDenotationType (Term fun) n ->
            [Term fun] ->
            MakeKnownM (Term fun)
        go sch f args = case (sch, args) of
            (RuntimeSchemeArrow sch', a : as) -> do
                res <- liftEither (f a)
                go sch' res as
            (RuntimeSchemeResult, []) -> f
            (RuntimeSchemeAll sch', _) -> go sch' f args
            -- TODO: can we make this function run in GenT MakeKnownM and generate arguments
            -- on the fly to avoid this error case?
            _ -> error $ "Wrong number of args for builtin " <> display bn <> ": " <> display args0

{- | Generate well-typed Term arguments to a builtin function.
 TODO: currently it only generates constant terms.
-}
genArgsWellTyped :: forall fun. ToBuiltinMeaning DefaultUni fun => fun -> Gen [Term fun]
genArgsWellTyped = genArgs $ \tr -> case genConstant tr of
    SomeGen gen -> Constant () . someValue <$> gen

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary :: forall fun. ToBuiltinMeaning DefaultUni fun => fun -> Gen [Term fun]
genArgsArbitrary = genArgs (const (runAstGen genTerm))

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs ::
    forall fun.
    ToBuiltinMeaning DefaultUni fun =>
    (forall (a :: GHC.Type). TypeRep a -> Gen (Term fun)) ->
    fun ->
    Gen [Term fun]
genArgs genArg bn = sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme (Term fun) args res -> [Gen (Term fun)]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning (Term fun) (CostingPart DefaultUni fun)
    meaning = toBuiltinMeaning bn

type family Head a where
    Head (x ': xs) = x

test_evaluation :: TestTree
test_evaluation =
    testGroup
        "evaluation"
        [ test_machines
        , test_builtinsDon'tThrow
        ]
