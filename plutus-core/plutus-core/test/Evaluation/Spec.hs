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
import PlutusCore.Generators (forAllNoShow, genValArg)
import PlutusCore.Generators.AST
import PlutusCore.Pretty

import Control.Exception
import Control.Monad.Except
import Control.Monad.Extra
import Data.Functor (($>))
import Data.List.Extra qualified as List
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property (failWith)
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection

type Term = PLC.Term TyName Name DefaultUni DefaultFun ()

test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
    testGroup
        "Builtins don't throw"
        $ fmap (\fun -> testProperty (display fun) $ prop_builtinsDon'tThrow fun) List.enumerate

prop_builtinsDon'tThrow :: DefaultFun -> Property
prop_builtinsDon'tThrow bn = property $ do
    args <- forAllNoShow . Gen.choice $ [genArgsWellTyped bn, genArgsArbitrary bn]
    mbErr <-
        liftIO $
            catch
                (($> Nothing) . evaluate . runEmitter . runExceptT $ eval args)
                (pure . pure)
    whenJust mbErr $ \(e :: SomeException) -> do
        let msg =
                "Builtin function evaluation failed"
                    <> "Function: "
                    <> display bn
                    <> "Arguments: "
                    <> display args
                    <> "Error: "
                    <> show e
        failWith Nothing msg
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
genArgsWellTyped = genArgs (fmap (Constant ()) . genValArg)

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary :: DefaultFun -> Gen [Term]
genArgsArbitrary = genArgs (const (runAstGen genTerm))

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs :: (forall k (a :: k). TypeRep a -> Gen Term) -> DefaultFun -> Gen [Term]
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
