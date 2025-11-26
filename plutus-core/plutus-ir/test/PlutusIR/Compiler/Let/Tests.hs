{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Compiler.Let.Tests where

import PlutusPrelude

import Control.Monad.Except
import Control.Monad.Reader (Reader, runReader)
import PlutusCore qualified as PLC
import PlutusIR.Compiler (Provenance (..))
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Compiler.Let
import PlutusIR.Pass.Test
import PlutusIR.Test
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

test_lets :: TestTree
test_lets =
  runTestNested
    ["plutus-ir", "test", "PlutusIR", "Compiler", "Let"]
    [ goldenPlcFromPir pTermAsProg "letInLet"
    , goldenPlcFromPir pTermAsProg "letDep"
    ]

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1876):
-- this fails because some of the let passes expect certain things to be
-- gone, e.g. non-strict bindings. We should a) add pre-/post-conditions for these,
-- and b) set up the tests to establish what is needed
test_propLets :: TestTree
test_propLets =
  ignoreTest $ testProperty "lets" $ \letKind ->
    withMaxSuccess 40000 $
      testPassProp' @_ @_ @_ @(Provenance ())
        (Original ())
        (\t -> fmap Original t)
        runCompiling
        (\tc -> compileLetsPassSC tc letKind)
  where
    -- This is rather painful, but it works
    runCompiling
      :: forall e m c
       . ( e ~ PIR.Error PLC.DefaultUni PLC.DefaultFun (Provenance ())
         , c ~ PIR.CompilationCtx PLC.DefaultUni PLC.DefaultFun ()
         , m ~ ExceptT e (ExceptT e (PLC.QuoteT (Reader c)))
         )
      => m () -> Either String ()
    runCompiling v =
      let
        res :: Either e ()
        res = do
          plcConfig <- modifyError (PIR.PLCError . PLC.TypeErrorE) $ PLC.getDefTypeCheckConfig (Original ())
          let ctx = PIR.toDefaultCompilationCtx plcConfig
          join $ flip runReader ctx $ PLC.runQuoteT $ runExceptT $ runExceptT v
       in
        convertToEitherString $ first void res

instance Arbitrary LetKind where
  arbitrary = elements [RecTerms, NonRecTerms, Types, DataTypes]
