{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
module TypecheckSpec where


import Control.Monad.Reader
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Utils
import PlutusCore.Quote
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Analysis.Builtins
import PlutusIR.Compiler
import PlutusIR.Compiler.Provenance (original)
import PlutusIR.Core
import PlutusIR.Generators.QuickCheck.GenerateTerms
import PlutusIR.Transform.Beta (beta)
import PlutusIR.Transform.CaseReduce (caseReduce)
import PlutusIR.Transform.CommuteFnWithConst (commuteFnWithConst)
import PlutusIR.Transform.EvaluateBuiltins (evaluateBuiltins)
import PlutusIR.Transform.Inline.Inline
import PlutusIR.Transform.StrictifyBindings
import PlutusIR.Transform.Unwrap (unwrapCancel)
import PlutusIR.TypeCheck
import PlutusPrelude (def)
import Test.QuickCheck (Property, withMaxSuccess)
import Test.Tasty (testGroup)
import Test.Tasty.ExpectedFailure
import Test.Tasty.Extras (TestNested)
import Test.Tasty.QuickCheck (testProperty)

-- | Typechecking property tests for all PIR compiler passes.
-- The argument allows the caller to scale the number of tests.
-- The default for the argument is @1@.
typecheck_test ::
  Int -> TestNested
typecheck_test factor = return $ testGroup "typechecking"
  [
  -- pure passes
    testProperty "unwrap pass" $
      withMaxSuccess (factor*3000) (prop_typecheck_pure unwrapCancel)
  , testProperty "caseReduce pass" $
      withMaxSuccess (factor*3000) (prop_typecheck_pure caseReduce)
  , testProperty "beta pass" $
      withMaxSuccess (factor*3000) (prop_typecheck_pure beta)
  , testProperty "commuteFnWithConst pass" $
      withMaxSuccess (factor*3000) (prop_typecheck_pure commuteFnWithConst)
  -- non-pure passes
  -- FIXME
  , expectFail $ testProperty "the whole simplifier pass" $
      withMaxSuccess (factor*3000) prop_typecheck
  , testProperty "strictifyBindings (Builtin Variant 1) pass" $
      withMaxSuccess (factor*3000) (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant1)
  , testProperty "strictifyBindings (Builtin Variant 2) pass" $
  withMaxSuccess (factor*3000) (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant2)
  , testProperty "evaluateBuiltins (Builtin Variant1) pass" $
  withMaxSuccess (factor*3000) (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant1)
  , testProperty "evaluateBuiltins (Builtin Variant2) pass" $
  withMaxSuccess (factor*3000) (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant2)
  -- FIXME
  , expectFail $ testProperty "inline (Builtin Variant1) pass" $
  withMaxSuccess (factor*3000) (prop_typecheck_inline DefaultFunSemanticsVariant1)
  -- FIXME
  , expectFail $ testProperty "inline (Builtin Variant2) pass" $
  withMaxSuccess (factor*3000) (prop_typecheck_inline DefaultFunSemanticsVariant2)
  ]

-- Convert Either Error () to Either String () to match with the Testable (Either String ())
-- instance.
convertToEitherString :: Either (Error DefaultUni DefaultFun ()) ()
  -> Either String ()
convertToEitherString = \case
  Left err -> Left $ show err
  Right () -> Right ()

-- | Typechecking a term after one of the pure passes.
tyCheckPure ::
  -- | The pure simplification pass.
  (Term TyName Name DefaultUni DefaultFun () -> Term TyName Name DefaultUni DefaultFun ())
  -> Term TyName Name DefaultUni DefaultFun ()
  -> Either (Error DefaultUni DefaultFun ()) ()
tyCheckPure pass tm = do
  config <- getDefTypeCheckConfig ()
  inferredType <- runQuoteT $ inferType config tm
  runQuoteT $ checkType config () (pass tm) inferredType

prop_typecheck_pure ::
  (Term TyName Name DefaultUni DefaultFun ()
  -> Term TyName Name DefaultUni DefaultFun ())
  -> Property
prop_typecheck_pure pass =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) -> do
  convertToEitherString $ tyCheckPure pass tm

-- | Typechecking a term after a `PlutusIR.Compiler.simplifyTerm` pass.
prop_typecheck :: Property
prop_typecheck =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
    config <- getDefTypeCheckConfig ()
    plcConfig <- PLC.getDefTypeCheckConfig ()
    inferredType <- runQuoteT $ inferType config tm
    case runReaderT (runQuoteT (simplifyTerm (original tm))) (toDefaultCompilationCtx plcConfig) of
      Left err -> Left $ void err
      Right simplified ->
        runQuoteT $ checkType config () (void simplified) inferredType

-- | Typechecking a term after a `PlutusIR.Transform.StrictifyBindings` pass.
prop_typecheck_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_strictifyBindings biVariant =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
    config <- getDefTypeCheckConfig ()
    inferredType <- runQuoteT $ inferType config tm
    let strictified = strictifyBindings (BuiltinsInfo biVariant) (original tm)
    runQuoteT $ checkType config () (void strictified) inferredType

-- | Typechecking a term after a `PlutusIR.Transform.EvaluateBuiltins` pass.
prop_typecheck_evaluateBuiltins :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_evaluateBuiltins biVariant =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
    config <- getDefTypeCheckConfig ()
    inferredType <- runQuoteT $ inferType config tm
    let evaluated = evaluateBuiltins True (BuiltinsInfo biVariant) def (original tm)
    runQuoteT $ checkType config () (void evaluated) inferredType

-- | Typechecking a term after a `PlutusIR.Transform.Inline` pass.
prop_typecheck_inline :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_inline biVariant =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
    config <- getDefTypeCheckConfig ()
    inferredType <- runQuoteT $ inferType config tm
    inlined <- runQuoteT $ inline mempty (BuiltinsInfo biVariant) (original tm)
    runQuoteT $ checkType config () (void inlined) inferredType

