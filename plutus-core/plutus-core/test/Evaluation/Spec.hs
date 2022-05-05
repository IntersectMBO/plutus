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
import Data.Ix
import Data.Kind qualified as GHC
import Data.List.Extra qualified as List
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection

type Term fun = PLC.Term TyName Name DefaultUni fun ()

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
            (\fun -> testProperty (display fun) $ prop_builtinEvaluation @DefaultFun fun gen f)
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
    toBuiltinMeaning AlwaysThrows = makeBuiltinMeaning f (\_ _ -> mempty)
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
            prop_builtinEvaluation @AlwaysThrows AlwaysThrows genArgsWellTyped f
        ]
  where
    f bn args = \case
        Left _ -> success
        Right _ -> do
            annotate "Except builtin function evaluation to throw exceptions, but it didn't"
            annotate $ "Function: " <> display bn
            annotate $ "Arguments: " <> display args
            failure

prop_builtinEvaluation ::
    forall fun.
    (ToBuiltinMeaning DefaultUni fun, Pretty fun) =>
    fun ->
    -- | A function making a generator for @fun@'s arguments.
    (fun -> Gen [Term fun]) ->
    -- | A function that takes a builtin function, a list of arguments, and the evaluation
    -- outcome, and decides whether to pass or fail the property.
    (fun -> [Term fun] -> Either SomeException (MakeKnownM (Term fun)) -> PropertyT IO ()) ->
    Property
prop_builtinEvaluation bn mkGen f = property $ do
    args <- forAllNoShow (mkGen bn) -- Gen.choice $ [genArgsWellTyped bn, genArgsArbitrary bn]
    f bn args
        =<< liftIO
            ( catch @SomeException
                (fmap Right . evaluate $ eval args)
                (pure . Left)
            )
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
        go sch fn args = case (sch, args) of
            (RuntimeSchemeArrow sch', a : as) -> do
                res <- liftEither (fn a)
                go sch' res as
            (RuntimeSchemeResult, []) -> fn
            (RuntimeSchemeAll sch', _) -> go sch' fn args
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
        , test_alwaysThrows
        ]
