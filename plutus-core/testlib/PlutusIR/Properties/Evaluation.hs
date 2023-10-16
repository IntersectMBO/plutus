{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LambdaCase        #-}


{- | All PIR compiler passes should satisfy the following property:
forall (p :: PIRProgram) . evaluate (compile p) == evaluate (compile (pass p))

It’s not totally straightforward to write this property because of the ==: how do we compare
the resulting programs? Comparing modulo alpha is not enough, consider:

\x -> (\y -> y) x

vs

\x -> x

These are “the same” program (they’re behaviourally equivalent), but showing that is tricky.

But we can do this for terms which are of a type whose values are always in normal form, which is
just builtin types atm - and this is what we are doing atm.
We have property-based tests for all our PIR passes based on this.
-}
module PlutusIR.Properties.Evaluation where

import Control.Monad.Reader
import PlutusCore.Core.Instance.Eq qualified as PLC
import PlutusCore.Core.Type qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.GenTm
import PlutusCore.Generators.QuickCheck.Utils
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Rename.Monad
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Compiler
import PlutusIR.Compiler.Lower
import PlutusIR.Core
import PlutusIR.Generators.QuickCheck.GenerateTerms
import PlutusPrelude (($>))
import Test.QuickCheck (Property)

-- Convert the Either from the evaluation to Either String () to match with the
-- Testable (Either String ()) instance.
convertToEitherString ::
  Either
    (CkEvaluationException DefaultUni DefaultFun) (PLC.Term TyName Name DefaultUni DefaultFun ())
  -> Either String (PLC.Term TyName Name DefaultUni DefaultFun ())
convertToEitherString = \case
  Left _   -> Left $ show "eqTermM returns Nothing"
  Right tm -> Right tm

-- | Evaluate a PIR term after a pure compiler pass.
evalPurePass ::
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> Term TyName Name DefaultUni DefaultFun (Provenance ()))
  -> BuiltinSemanticsVariant DefaultFun
  -> Term TyName Name DefaultUni DefaultFun (Provenance ()) ->
  Either
    String
    (PLC.Term TyName Name DefaultUni DefaultFun ())
evalPurePass pass biVariant pirTm = do
  -- let plcConfig = first display $ PLC.getDefTypeCheckConfig ()
  plcConfig <- PLC.getDefTypeCheckConfig (Original ())
  lowered <- flip runReaderT (toDefaultCompilationCtx plcConfig) $
    runQuoteT $ lowerTerm $ pass (Original () <$ pirTm)
  convertToEitherString $
    evaluateCkNoEmit (defaultBuiltinsRuntimeForSemanticsVariant biVariant) (lowered $> ())

-- | Evaluate a PIR term that is lowered to a PLC term without any PIR pass.
evalNoPass :: BuiltinSemanticsVariant DefaultFun
  -> Term TyName Name DefaultUni DefaultFun (Provenance ()) ->
  Either String (PLC.Term TyName Name DefaultUni DefaultFun ())
evalNoPass = evalPurePass id

-- | Evaluate a PIR term after a pure compiler pass.
evalNonPurePass ::
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (ReaderT (CompilationCtx DefaultUni DefaultFun ()) (Either String))
      (Term TyName Name DefaultUni DefaultFun (Provenance ())))
  -> BuiltinSemanticsVariant DefaultFun
  -> Term TyName Name DefaultUni DefaultFun b
  -> Either String (PLC.Term TyName Name DefaultUni DefaultFun ())
evalNonPurePass pass biVariant pirTm = do
  -- let plcConfig = first display $ PLC.getDefTypeCheckConfig ()
  plcConfig <- PLC.getDefTypeCheckConfig (Original ())
  lowered <- flip runReaderT (toDefaultCompilationCtx plcConfig) $
    runQuoteT $ lowerTerm =<< pass (Original () <$ pirTm)
  convertToEitherString $
    evaluateCkNoEmit (defaultBuiltinsRuntimeForSemanticsVariant biVariant) (lowered $> ())

-- | Generate builtin types. See this module's haddock.
genBuiltInTypeKind :: Gen (Term TyName Name DefaultUni DefaultFun ())
genBuiltInTypeKind = do
  -- genTermOfType can only handle Type kind.
  someTy <- genBuiltinTypeOf (Type ())
  case someTy of
    Just someBiType -> runGenTm $ genTermOfType $ TyBuiltin () someBiType
    Nothing         -> genBuiltInTypeKind -- try again if not successful

-- | Check that a pure pass preserves evaluation behaviour.
pureEvaluationProp ::
  -- | The pure PIR compiler pass.
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> Term TyName Name DefaultUni DefaultFun (Provenance ()))
  -> BuiltinSemanticsVariant DefaultFun
  -> Property
pureEvaluationProp pass biVariant =
  forAllDoc "ty,tm" genBuiltInTypeKind (const []) $ \tm -> do
    -- the generated term may not have globally unique names
    renamed <- runQuoteT $ rename tm
    evaluatedNoPass <- evalNoPass biVariant (Original () <$ renamed)
    evaluatedAfterPass <-
      evalPurePass pass biVariant (Original () <$ renamed)
    let isEq = runRenameT $ PLC.eqTermM evaluatedNoPass evaluatedAfterPass
    case isEq of
      Just _  -> Right ()
      Nothing -> Left $
        "Evaluation behaviour not preserved. Before the pass, the term evaluates to \n"
        <> display evaluatedNoPass <> "\n but after the pass it evaluates to \n"
        <> display evaluatedAfterPass

-- | Check that a non-pure pass preserves evaluation behaviour.
nonPureEvaluationProp ::
  -- The non-pure PIR compiler pass.
  (Term TyName Name DefaultUni DefaultFun (Provenance ())
  -> QuoteT
      (ReaderT (CompilationCtx DefaultUni DefaultFun ()) (Either String))
      (Term TyName Name DefaultUni DefaultFun (Provenance ())))
  -> BuiltinSemanticsVariant DefaultFun
  -> Property
nonPureEvaluationProp pass biVariant =
  forAllDoc "ty,tm" genBuiltInTypeKind (const []) $ \tm -> do
    -- the generated term may not have globally unique names
    renamed <- runQuoteT $ rename tm
    evaluatedNoPass <- evalNoPass biVariant (Original () <$ renamed)
    evaluatedAfterPass <-
      evalNonPurePass pass biVariant (Original () <$ renamed)
    let isEq = runRenameT $ PLC.eqTermM evaluatedNoPass evaluatedAfterPass
    case isEq of
      Just _  -> Right ()
      Nothing -> Left $
        "Evaluation behaviour not preserved. Before the pass, the term evaluates to \n"
        <> display evaluatedNoPass <> "\n but after the pass it evaluates to \n"
        <> display evaluatedAfterPass

-- | Check that a non-pure pass that requires extra constraints preserves evaluation behaviour.
-- extraConstraintTypecheckProp ::
--   (Term TyName Name DefaultUni DefaultFun (Provenance ())
--   -> QuoteT
--       (ReaderT
--          (CompilationCtx DefaultUni DefaultFun c)
--          (Either (Error DefaultUni DefaultFun b)))
--       (Term TyName Name DefaultUni DefaultFun a))
--   -> Property
-- extraConstraintTypecheckProp pass =
--   forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (_ty, tm) -> do
--     config <- getDefTypeCheckConfig ()
--     plcConfig <- PLC.getDefTypeCheckConfig ()
--     let processed =
--           flip runReaderT (toDefaultCompilationCtx plcConfig) $
--             runQuoteT $ pass =<< rename (Original () <$ tm)
--     case processed of
--       Left err -> Left $ err $> ()
--       Right processSuccess -> do
--         _ <- runQuoteT $ do
--           -- need to rename because some passes don't preserve global uniqueness
--           renamedProcessed <- rename processSuccess
--           inferType config (renamedProcessed $> ())
--         pure ()
