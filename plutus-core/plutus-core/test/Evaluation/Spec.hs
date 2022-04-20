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
import PlutusCore.Generators (GenArbitraryTerm (..), GenTypedTerm (..), forAllNoShow)
import PlutusCore.Pretty

import Control.Exception
import Control.Monad.Except
import Data.Ix
import Data.Kind qualified as GHC
import Data.List.Extra qualified as List
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection

type Term uni fun = PLC.Term TyName Name uni fun ()

{- | Evaluating a builtin function should never throw any exception (the evaluation is allowed
 to fail with a `KnownTypeError`, of course).

 The test covers both succeeding and failing evaluations and verifies that in either case
 no exception is thrown. The failing cases use arbitrary `Term` arguments (which doesn't
 guarantee failure, but most likely), and the succeeding cases generate `Term` arguments
 based on a builtin function's `TypeScheme`. For `Opaque` arguments it generates arbitrary
 `Term`s (which technically doesn't guarantee evaluation success, although it is the case
 with all current builtin functions).
-}
test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
    testGroup
        "Builtins don't throw"
        $ fmap
            ( \fun ->
                testProperty (display fun) $
                    prop_builtinEvaluation @_ @DefaultFun fun gen f
            )
            List.enumerate
  where
    gen bn = Gen.choice [genArgsWellTyped bn, genArgsArbitrary bn]
    f bn args = \case
        Left e -> do
            annotate "Builtin function evaluation failed"
            annotate $ "Function: " <> display bn
            annotate $ "Arguments: " <> display args
            annotate $ "Error " <> show e
            failure
        Right _ -> success

data AlwaysThrows
    = -- | A builtin function whose denotation always throws an exception.
      AlwaysThrows
    deriving stock (Eq, Ord, Show, Bounded, Enum, Ix)

instance Pretty AlwaysThrows where
    pretty = pretty . show

instance uni ~ DefaultUni => ToBuiltinMeaning uni AlwaysThrows where
    type CostingPart uni AlwaysThrows = ()
    toBuiltinMeaning _ver AlwaysThrows = makeBuiltinMeaning f mempty
      where
        f :: Integer -> Integer
        f _ = error "This builtin function always throws an exception."

{- | This test verifies that if evaluating a builtin function actually throws an exception,
 we'd get a `Left` value, which would cause `test_builtinsDon'tThrow` to fail.
-}
test_alwaysThrows :: TestTree
test_alwaysThrows =
    testGroup
        "Builtins throwing exceptions should cause tests to fail"
        [ testProperty (display AlwaysThrows) $
            prop_builtinEvaluation @_ @AlwaysThrows AlwaysThrows genArgsWellTyped f
        ]
  where
    f bn args = \case
        Left _ -> success
        Right _ -> do
            annotate "Expect builtin function evaluation to throw exceptions, but it didn't"
            annotate $ "Function: " <> display bn
            annotate $ "Arguments: " <> display args
            failure

prop_builtinEvaluation ::
    forall uni fun.
    (ToBuiltinMeaning uni fun, Pretty fun, Closed uni, GShow uni, uni `Everywhere` PrettyConst) =>
    fun ->
    -- | A function making a generator for @fun@'s arguments.
    (fun -> Gen [Term uni fun]) ->
    -- | A function that takes a builtin function, a list of arguments, and the evaluation
    -- outcome, and decides whether to pass or fail the property.
    (fun -> [Term uni fun] -> Either SomeException (MakeKnownM (Term uni fun)) -> PropertyT IO ()) ->
    Property
prop_builtinEvaluation bn mkGen f = property $ do
    args <- forAllNoShow (mkGen bn)
    f bn args =<< liftIO (try @SomeException . evaluate $ eval args)
  where
    meaning :: BuiltinMeaning (Term uni fun) (CostingPart uni fun)
    meaning = toBuiltinMeaning (defaultVersion ()) bn

    eval :: [Term uni fun] -> MakeKnownM (Term uni fun)
    eval args0 = case meaning of
        BuiltinMeaning _ _ runtime -> go (_broRuntimeScheme runtime) (_broImmediateF runtime) args0
      where
        go ::
            forall n.
            RuntimeScheme n ->
            ToRuntimeDenotationType (Term uni fun) n ->
            [Term uni fun] ->
            MakeKnownM (Term uni fun)
        go sch fn args = case (sch, args) of
            (RuntimeSchemeArrow sch', a : as) -> do
                res <- liftReadKnownM (fn a)
                go sch' res as
            (RuntimeSchemeResult, []) -> fn
            (RuntimeSchemeAll sch', _) -> go sch' fn args
            -- TODO: can we make this function run in GenT MakeKnownM and generate arguments
            -- on the fly to avoid this error case?
            _ -> error $ "Wrong number of args for builtin " <> display bn <> ": " <> display args0

genArgsWellTyped ::
    forall uni fun.
    (GenTypedTerm uni, ToBuiltinMeaning uni fun) =>
    fun ->
    Gen [Term uni fun]
genArgsWellTyped = genArgs genTypedTerm

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary ::
    forall uni fun.
    (GenArbitraryTerm uni, ToBuiltinMeaning uni fun) =>
    fun ->
    Gen [Term uni fun]
genArgsArbitrary = genArgs (\_ -> genArbitraryTerm @uni)

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs ::
    forall uni fun.
    ToBuiltinMeaning uni fun =>
    (forall (a :: GHC.Type). TypeRep a -> Gen (Term uni fun)) ->
    fun ->
    Gen [Term uni fun]
genArgs genArg bn = sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme (Term uni fun) args res -> [Gen (Term uni fun)]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning (Term uni fun) (CostingPart uni fun)
    meaning = toBuiltinMeaning (defaultVersion ()) bn

type family Head a where
    Head (x ': xs) = x

test_evaluation :: TestTree
test_evaluation =
    testGroup
        "evaluation"
        [ test_machines
        , test_builtinsDon'tThrow
        , test_alwaysThrows
        ]
