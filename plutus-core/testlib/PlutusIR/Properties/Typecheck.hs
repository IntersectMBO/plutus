{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-orphans #-}


{- | Typechecking property tests for all PIR compiler passes. Currently we only typecheck the term
 after a pass.

 There were test failures when we infer the type before a pass and check that the
 type after a pass is the same. The failures are probably caused by the
 `PlutusIR.TypeCheck.AllowEscape` typechecker config.
-}
module PlutusIR.Properties.Typecheck where

import Control.Monad.Reader
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Utils
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Compiler
import PlutusIR.Compiler.Provenance (original)
import PlutusIR.Core
import PlutusIR.Generators.QuickCheck.GenerateTerms
import PlutusIR.TypeCheck
import PlutusPrelude (($>))
import Test.QuickCheck (Property, elements)
import Test.QuickCheck.Arbitrary

instance Arbitrary (BuiltinSemanticsVariant DefaultFun) where
    arbitrary = elements [DefaultFunSemanticsVariant1, DefaultFunSemanticsVariant2]

-- Convert Either Error () to Either String () to match with the Testable (Either String ())
-- instance.
convertToEitherString :: Either (Error DefaultUni DefaultFun ()) ()
  -> Either String ()
convertToEitherString = \case
  Left err -> Left $ show err
  Right () -> Right ()

-- | Check that a term typechecks after one of the pure passes.
pureTypecheckProp ::
  -- | The pure simplification pass.
  (Term TyName Name DefaultUni DefaultFun ()
  -> Term TyName Name DefaultUni DefaultFun ())
  -> Property
pureTypecheckProp pass =
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      _ <- runQuoteT $ inferType config (pass renamed)
      pure ()

-- | Check that a term typechecks after a non-pure pass.
nonPureTypecheckProp :: (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (Either (Error DefaultUni DefaultFun ()))
      (Term TyName Name DefaultUni DefaultFun a))
  -> Property
nonPureTypecheckProp pass =
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (_ty, tm) ->
    convertToEitherString $ do
      config <- getDefTypeCheckConfig ()
      -- the generated term may not have globally unique names
      renamed <- runQuoteT $ rename tm
      processed <- runQuoteT $ pass (original renamed)
      _ <- runQuoteT $ inferType config (processed $> ())
      pure ()

-- | Check that a term typechecks after a non-pure pass that requires extra constraints.
extraConstraintTypecheckProp ::
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (ReaderT
         (CompilationCtx DefaultUni DefaultFun c)
         (Either (Error DefaultUni DefaultFun b)))
      (Term TyName Name DefaultUni DefaultFun a))
  -> Property
extraConstraintTypecheckProp pass =
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (_ty, tm) ->
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
