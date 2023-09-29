{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
module TypecheckSpec where


import Control.Monad.Reader
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Utils
import PlutusCore.Quote
import PlutusCore.Rename
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
import PlutusPrelude (def, ($>))
import Test.QuickCheck (Property, withMaxSuccess)
import Test.Tasty (testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Extras (TestNested)
import Test.Tasty.QuickCheck (testProperty)

-- | Typechecking property tests for all PIR compiler passes.
typecheck_test :: TestNested
typecheck_test = return $ testGroup "typechecking"
  [
  -- pure passes
    testProperty "unwrap pass" $
      withMaxSuccess 3000 (prop_typecheck_pure unwrapCancel)
  , testProperty "caseReduce pass" $
      withMaxSuccess 3000 (prop_typecheck_pure caseReduce)
  , testProperty "beta pass" $
      withMaxSuccess 3000 (prop_typecheck_pure beta)
  , testProperty "commuteFnWithConst pass" $
      withMaxSuccess 3000 (prop_typecheck_pure commuteFnWithConst)
  , testProperty "strictifyBindings (Builtin Variant 1) pass" $
      withMaxSuccess 3000 (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant1)
  , testProperty "strictifyBindings (Builtin Variant 2) pass" $
      withMaxSuccess 3000 (prop_typecheck_strictifyBindings DefaultFunSemanticsVariant2)
  , testProperty "evaluateBuiltins (Builtin Variant 1) pass" $
      withMaxSuccess 3000 (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant1)
  , testProperty "evaluateBuiltins (Builtin Variant 2) pass" $
      withMaxSuccess 3000 (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant2)

  -- non-pure passes

  -- FIXME
  , expectFail $ testProperty "the whole simplifier pass" $
      withMaxSuccess 3000 prop_typecheck_simplify

  -- FIXME
  , expectFail $ testProperty "inline (Builtin Variant1) pass" $
  withMaxSuccess 3000 (prop_typecheck_inline DefaultFunSemanticsVariant1)

  -- FIXME
  , expectFail $ testProperty "inline (Builtin Variant2) pass" $
  withMaxSuccess 3000 (prop_typecheck_inline DefaultFunSemanticsVariant2)
  ]

-- Convert Either Error () to Either String () to match with the Testable (Either String ())
-- instance.
convertToEitherString :: Either (Error DefaultUni DefaultFun ()) ()
  -> Either String ()
convertToEitherString = \case
  Left err -> Left $ show err
  Right () -> Right ()

-- | Check that a term has the same type before and after one of the pure passes.
prop_typecheck_pure ::
  -- | The pure simplification pass.
  (Term TyName Name DefaultUni DefaultFun ()
  -> Term TyName Name DefaultUni DefaultFun ())
  -> Property
prop_typecheck_pure pass =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      inferredType <- runQuoteT $ inferType config renamed
      runQuoteT $ checkType config () (pass renamed) inferredType

-- | Check that a term has the same type before and after the `PlutusIR.Compiler.simplifyTerm` pass.
prop_typecheck_simplify :: Property
prop_typecheck_simplify =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      plcConfig <- PLC.getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      inferredType <- runQuoteT $ inferType config renamed
      let simplified =
            runReaderT
              (runQuoteT (simplifyTerm (original renamed))) (toDefaultCompilationCtx plcConfig)
      case simplified of
        Left err -> Left $ err $> ()
        Right simplifiedSuccess ->
          runQuoteT $ checkType config () (simplifiedSuccess $> ()) inferredType

-- | Check that a term has the same type before and after a
-- `PlutusIR.Transform.StrictifyBindings` pass.
prop_typecheck_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_strictifyBindings biVariant =
  prop_typecheck_pure (strictifyBindings (BuiltinsInfo biVariant))

-- | Check that a term has the same type before and after a `PlutusIR.Transform.EvaluateBuiltins`
-- pass.
prop_typecheck_evaluateBuiltins :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_evaluateBuiltins biVariant =
  prop_typecheck_pure (evaluateBuiltins True (BuiltinsInfo biVariant) def)

-- | Check that a term has the same type before and after a `PlutusIR.Transform.Inline` pass.
prop_typecheck_inline :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_inline biVariant =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      inferredType <- runQuoteT $ inferType config renamed
      inlined <- runQuoteT $ inline mempty (BuiltinsInfo biVariant) (original renamed)
      runQuoteT $ checkType config () (inlined $> ()) inferredType

