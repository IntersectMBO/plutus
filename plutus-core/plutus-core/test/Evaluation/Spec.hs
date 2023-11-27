-- editorconfig-checker-disable-file
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
import PlutusCore.Builtin as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExBudgetStream (ExBudgetStream (..))
import PlutusCore.Generators.Hedgehog (GenArbitraryTerm (..), GenTypedTerm (..), forAllNoShow)
import PlutusCore.Pretty
import PlutusPrelude

import Control.Exception
import Control.Monad.IO.Class (liftIO)
import Data.Ix
import Data.Kind qualified as GHC
import Evaluation.Machines (test_machines)
import GHC.Exts (fromString)
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
    testGroup "Builtins don't throw" $
        enumerate @(BuiltinSemanticsVariant DefaultFun) <&> \semvar ->
            testGroup (fromString . render $ "Version: " <> pretty semvar) $
                let runtimes = toBuiltinsRuntime semvar defaultBuiltinCostModel
                in enumerate @DefaultFun <&> \fun ->
                    -- Perhaps using @maxBound@ (with @Enum@, @Bounded@) is indeed better than
                    -- @Default@ for BuiltinSemanticsVariants
                    testPropertyNamed
                        (display fun)
                        (fromString $ display fun)
                        (prop_builtinEvaluation runtimes fun gen f)
  where
    gen bn = Gen.choice [genArgsWellTyped def bn, genArgsArbitrary def bn]
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
    data BuiltinSemanticsVariant AlwaysThrows = AlwaysThrowsSemanticsVariant1

    toBuiltinMeaning _semvar AlwaysThrows = makeBuiltinMeaning f $ \_ _ -> ExBudgetLast mempty
      where
        f :: Integer -> Integer
        f _ = error "This builtin function always throws an exception."

instance Default (BuiltinSemanticsVariant AlwaysThrows) where
    def = AlwaysThrowsSemanticsVariant1

{- | This test verifies that if evaluating a builtin function actually throws an exception,
 we'd get a `Left` value, which would cause `test_builtinsDon'tThrow` to fail.
-}
test_alwaysThrows :: TestTree
test_alwaysThrows =
    testGroup
        "Builtins throwing exceptions should cause tests to fail"
        [ testPropertyNamed (display AlwaysThrows) (fromString . display $ AlwaysThrows) $
            prop_builtinEvaluation @_ @AlwaysThrows runtimes AlwaysThrows (genArgsWellTyped semvar) f
        ]
  where
    semvar = AlwaysThrowsSemanticsVariant1
    runtimes = toBuiltinsRuntime semvar ()
    f bn args = \case
        Left _ -> success
        Right _ -> do
            annotate "Expect builtin function evaluation to throw exceptions, but it didn't"
            annotate $ "Function: " <> display bn
            annotate $ "Arguments: " <> display args
            failure

prop_builtinEvaluation ::
    forall uni fun.
    (PrettyUni uni, Pretty fun) =>
    BuiltinsRuntime fun (Term uni fun) ->
    fun ->
    -- | A function making a generator for @fun@'s arguments.
    (fun -> Gen [Term uni fun]) ->
    -- | A function that takes a builtin function, a list of arguments, and the evaluation
    -- outcome, and decides whether to pass or fail the property.
    (fun -> [Term uni fun] -> Either SomeException (MakeKnownM (Term uni fun)) -> PropertyT IO ()) ->
    Property
prop_builtinEvaluation runtimes bn mkGen f = property $ do
    args0 <- forAllNoShow $ mkGen bn
    let
        eval :: [Term uni fun] -> BuiltinRuntime (Term uni fun) -> MakeKnownM (Term uni fun)
        eval [] (BuiltinResult _ getX) =
            getX
        eval (arg : args) (BuiltinExpectArgument toRuntime) =
            eval args (toRuntime arg)
        eval args (BuiltinExpectForce runtime) =
            eval args runtime
        eval _ _ =
            -- TODO: can we make this function run in @GenT MakeKnownM@ and generate arguments
            -- on the fly to avoid this error case?
            error $ "Wrong number of args for builtin " <> display bn <> ": " <> display args0
        runtime0 = lookupBuiltin bn runtimes
    f bn args0 =<< liftIO (try @SomeException . evaluate $ eval args0 runtime0)

genArgsWellTyped ::
    forall uni fun.
    (GenTypedTerm uni, ToBuiltinMeaning uni fun)
    => PLC.BuiltinSemanticsVariant fun
    -> fun
    -> Gen [Term uni fun]
genArgsWellTyped semvar = genArgs semvar genTypedTerm

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary ::
    forall uni fun.
    (GenArbitraryTerm uni, ToBuiltinMeaning uni fun)
    => PLC.BuiltinSemanticsVariant fun
    -> fun ->
    Gen [Term uni fun]
genArgsArbitrary semvar = genArgs semvar (\_ -> genArbitraryTerm @uni)

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs ::
    forall uni fun.
    ToBuiltinMeaning uni fun
    => PLC.BuiltinSemanticsVariant fun
    -> (forall (a :: GHC.Type). TypeRep a -> Gen (Term uni fun))
    -> fun
    -> Gen [Term uni fun]
genArgs semvar genArg bn = sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme (Term uni fun) args res -> [Gen (Term uni fun)]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning (Term uni fun) (CostingPart uni fun)
    meaning = toBuiltinMeaning semvar bn

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
