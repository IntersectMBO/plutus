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
import PlutusCore.Generators (forAllNoShow, genConstant)
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

type Term = PLC.Term TyName Name DefaultUni DefaultFun ()

test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
    testGroup
        "Builtins don't throw"
        $ fmap (\fun -> testProperty (display fun) $ prop_builtinsDon'tThrow fun) List.enumerate

-- | Evaluating a builtin function should never throw any exception (the evaluation is allowed
-- to fail with a `KnownTypeError`, of course).
--
-- The test covers both succeeding and failing evaluations and verifies that in either case
-- no exception is thrown. The failing cases use arbitrary `Term` arguments (which doesn't
-- guarantee failure, but most likely), and the succeeding cases generate `Term` arguments
-- based on a builtin function's `TypeScheme`. For `Opaque` arguments it generates arbitrary
-- `Term`s (which technically doesn't guarantee evaluation success, although it is the case
-- with all current builtin functions).
prop_builtinsDon'tThrow :: DefaultFun -> Property
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
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning bn

    eval :: [Term] -> MakeKnownM Term
    eval args0 = case meaning of
        BuiltinMeaning _ _ runtime -> go (_broRuntimeScheme runtime) (_broImmediateF runtime) args0
      where
        go ::
            forall n.
            RuntimeScheme n ->
            ToRuntimeDenotationType Term n ->
            [Term] ->
            MakeKnownM Term
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
genArgsWellTyped :: DefaultFun -> Gen [Term]
genArgsWellTyped = genArgs (fmap mkTerm . genConstant)
  where
    mkTerm :: forall (a :: GHC.Type). MakeKnown Term a => a -> Term
    mkTerm a = case runEmitter . runExceptT $ makeKnown a of
        (Right term, _) -> term
        _               -> error "genArgsWellTyped: got error from makeKnown"

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary :: DefaultFun -> Gen [Term]
genArgsArbitrary = genArgs (const (runAstGen genTerm))

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs ::
    (forall (a :: GHC.Type). MakeKnown Term a => TypeRep a -> Gen Term) ->
    DefaultFun ->
    Gen [Term]
genArgs genArg bn = sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme Term args res -> [Gen Term]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
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
