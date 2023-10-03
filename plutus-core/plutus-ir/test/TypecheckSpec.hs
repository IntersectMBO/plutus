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
import PlutusIR.Compiler.Let
import PlutusIR.Compiler.Provenance (original)
import PlutusIR.Core
import PlutusIR.Generators.QuickCheck.GenerateTerms
import PlutusIR.Transform.Beta (beta)
import PlutusIR.Transform.CaseReduce (caseReduce)
import PlutusIR.Transform.CommuteFnWithConst (commuteFnWithConst)
import PlutusIR.Transform.EvaluateBuiltins (evaluateBuiltins)
import PlutusIR.Transform.Inline.Inline
import PlutusIR.Transform.LetFloatIn (floatTerm)
import PlutusIR.Transform.StrictifyBindings
import PlutusIR.Transform.Unwrap (unwrapCancel)
import PlutusIR.TypeCheck
import PlutusPrelude (def, ($>))
import Test.QuickCheck (Property, withMaxSuccess)
import Test.Tasty (testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Extras (TestNested)
import Test.Tasty.QuickCheck (testProperty)

{- | Typechecking property tests for all PIR compiler passes. Currently we only typecheck the term
 after a pass.

 There were test failures when we infer the type before a pass and check that the
 type after a pass is the same. The failures are probably caused by the
 `PlutusIR.TypeCheck.AllowEscape` typechecker config.
-}
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

  , testProperty "the whole simplifier pass" $
      withMaxSuccess 3000 prop_typecheck_simplify

  , testProperty "inline (Builtin Variant1) pass" $
  withMaxSuccess 3000 (prop_typecheck_inline DefaultFunSemanticsVariant1)

  , testProperty "inline (Builtin Variant2) pass" $
  withMaxSuccess 3000 (prop_typecheck_inline DefaultFunSemanticsVariant2)

  , testProperty "floatTerm pass" $
      withMaxSuccess 3000 prop_typecheck_floatTerm

  -- FIXME
  , expectFail $ testProperty "compileLets pass (recursive terms)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_RecTerms

  , testProperty "compileLets pass (non-recursive terms)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_NonRecTerms

  , testProperty "compileLets pass (types)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_Types

  -- FIXME
  , expectFail $ testProperty "compileLets pass (data types)" $
      withMaxSuccess 3000 prop_typecheck_compileLets_DataTypes
  ]

-- Convert Either Error () to Either String () to match with the Testable (Either String ())
-- instance.
convertToEitherString :: Either (Error DefaultUni DefaultFun ()) ()
  -> Either String ()
convertToEitherString = \case
  Left err -> Left $ show err
  Right () -> Right ()

-- | Check that a term typechecks after one of the pure passes.
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
      _ <- runQuoteT $ inferType config (pass renamed)
      pure ()

-- | Check that a term typechecks after a
-- `PlutusIR.Transform.StrictifyBindings` pass.
prop_typecheck_strictifyBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_strictifyBindings biVariant =
  prop_typecheck_pure (strictifyBindings (BuiltinsInfo biVariant))

-- | Check that a term typechecks after a `PlutusIR.Transform.EvaluateBuiltins`
-- pass.
prop_typecheck_evaluateBuiltins :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_evaluateBuiltins biVariant =
  prop_typecheck_pure (evaluateBuiltins True (BuiltinsInfo biVariant) def)

-- | Check that a term typechecks after a non-pure pass.
prop_typecheck_non_pure :: (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (Either (Error DefaultUni DefaultFun ()))
      (Term TyName Name DefaultUni DefaultFun a))
  -> Property
prop_typecheck_non_pure pass =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      processed <- runQuoteT $ pass (original renamed)
      _ <- runQuoteT $ inferType config (processed $> ())
      pure ()

-- | Check that a term typechecks after a `PlutusIR.Transform.Inline` pass.
prop_typecheck_inline :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_inline biVariant =
  prop_typecheck_non_pure (inline mempty (BuiltinsInfo biVariant))

-- | Check that a term typechecks after a
-- `PlutusIR.Transform.LetFloatIn.floatTerm` pass.
prop_typecheck_floatTerm :: Property
prop_typecheck_floatTerm =
  prop_typecheck_non_pure $ floatTerm def True

-- | Check that a term typechecks after the `PlutusIR.Compiler.simplifyTerm` pass.
prop_typecheck_simplify :: Property
prop_typecheck_simplify = prop_typecheck_extra_constraint simplifyTerm

prop_typecheck_extra_constraint ::
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (ReaderT
         (CompilationCtx DefaultUni DefaultFun c)
         (Either (Error DefaultUni DefaultFun b)))
      (Term TyName Name DefaultUni DefaultFun a))
  -> Property
prop_typecheck_extra_constraint pass =
  -- generate type and term in debug mode for easier debugging
  forAllDoc "ty,tm" genTypeAndTermDebug_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      plcConfig <- PLC.getDefTypeCheckConfig ()
      renamed <- runQuoteT $ rename tm
      let processed =
            runReaderT
              (runQuoteT (pass (original renamed))) (toDefaultCompilationCtx plcConfig)
      case processed of
        Left err -> Left $ err $> ()
        Right processSuccess -> do
          -- need to rename because some passes don't preserve global uniqueness
          renamedProcessed <- runQuoteT $ rename processSuccess
          _ <- runQuoteT $ inferType config (renamedProcessed $> ())
          pure ()

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (recursive terms) pass.
prop_typecheck_compileLets_RecTerms :: Property
prop_typecheck_compileLets_RecTerms =
  prop_typecheck_extra_constraint (compileLets RecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (non-recursive terms) pass.
prop_typecheck_compileLets_NonRecTerms :: Property
prop_typecheck_compileLets_NonRecTerms =
  prop_typecheck_extra_constraint (compileLets NonRecTerms)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (types) pass.
prop_typecheck_compileLets_Types :: Property
prop_typecheck_compileLets_Types =
  prop_typecheck_extra_constraint (compileLets Types)

-- | Check that a term typechecks after a
-- `PlutusIR.Compiler.Let.compileLets` (data types) pass.
prop_typecheck_compileLets_DataTypes :: Property
prop_typecheck_compileLets_DataTypes =
  prop_typecheck_extra_constraint (compileLets DataTypes)
