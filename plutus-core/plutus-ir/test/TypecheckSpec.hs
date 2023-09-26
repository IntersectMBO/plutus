{-# LANGUAGE TypeFamilies #-}
module TypecheckSpec where


import Control.Monad.Reader
import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Utils
import PlutusCore.Quote
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Compiler
import PlutusIR.Compiler.Provenance (original)
import PlutusIR.Core
import PlutusIR.Generators.QuickCheck.GenerateTerms
import PlutusIR.TypeCheck
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

-- | Typechecking property tests for all PIR compiler passes.
-- The argument allows the caller to scale the number of tests.
-- The default for the argument is @1@.
typecheck_test ::
  Int -> TestNested
typecheck_test factor = return $ testGroup "typechecking"
  [ testProperty "simplifierPass" $
      withMaxSuccess (factor*3000) prop_typecheck
  ]

tyCheck ::
  Term TyName Name DefaultUni DefaultFun ()
  -> Either (Error DefaultUni DefaultFun ()) ()
tyCheck tm = do
  config <- getDefTypeCheckConfig ()
  plcConfig <- PLC.getDefTypeCheckConfig ()
  inferredType <- runQuoteT $ inferType config tm
  case runReaderT (runQuoteT (simplifyTerm (original tm))) (toDefaultCompilationCtx plcConfig) of
    Left err -> Left $ void err
    Right simplified ->
      runQuoteT $ checkType config () (void simplified) inferredType

prop_typecheck :: Property
prop_typecheck =
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (_ty, tm) -> do
  case tyCheck tm of
    Left err -> Left $ show err
    Right () -> Right ()

