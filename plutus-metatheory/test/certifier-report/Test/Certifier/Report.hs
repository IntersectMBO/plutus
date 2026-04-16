{-# LANGUAGE TemplateHaskell #-}

module Test.Certifier.Report where

import Certifier
import Paths_plutus_metatheory (getDataDir)
import PlutusCore qualified as PLC
import PlutusCore.Default.Builtins
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Executable.Eval (evalCounting, evalOptimizerTrace, mkDefaultEvalCtx)
import PlutusCore.Quote
import PlutusLedgerApi.Common
import PlutusPrelude (def, unsafeFromRight)
import PlutusTx qualified as Tx
import PlutusTx.Lift (lift)
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Trace

import Control.Lens ((&), (.~))
import Control.Monad.Trans.Except
import Data.Bifunctor
import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS
import Data.Foldable qualified as F
import Data.Functor
import System.FilePath
import System.IO.Extra

import Test.Tasty
import Test.Tasty.Golden

loadFrom :: FilePath -> IO (OptimizerTrace Name DefaultUni DefaultFun ())
loadFrom name = do
  root <- getDataDir
  prog <-
    UPLC.programMapNames UPLC.fakeNameDeBruijn . uncheckedDeserialiseUPLC . SBS.toShort
      <$> B.readFile (root </> "test" </> "certifier-report" </> "scripts" </> name)
  let term =
        either
          ( \e ->
              error $
                "loadFrom: program from "
                  <> name
                  <> " is ill-scoped: "
                  <> show e
          )
          id
          . runQuote
          . runExceptT
          $ UPLC.unDeBruijnTerm (UPLC._progTerm prog)
  pure . runQuote $ snd <$> simplify term

simplify
  :: Term Name DefaultUni DefaultFun ()
  -> Quote
       ( Term Name DefaultUni DefaultFun ()
       , OptimizerTrace Name DefaultUni DefaultFun ()
       )
simplify =
  runOptimizerT
    . termOptimizer
      ( defaultOptimizeOpts
          & ooPreserveLogging .~ False
      )
      def

evalCtx :: EvaluationContext
evalCtx = mkDefaultEvalCtx def
{-# OPAQUE evalCtx #-}

evalTrace
  :: OptimizerTrace Name DefaultUni DefaultFun ()
  -> [Term NamedDeBruijn DefaultUni DefaultFun ()]
  -> [ ( Maybe (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       , ExBudget
       )
     ]
evalTrace trace args =
  first (either Just (const Nothing)) . evalCounting evalCtx newestPV
    <$> appliedTerms
  where
    appliedTerms :: [Term NamedDeBruijn DefaultUni DefaultFun ()]
    appliedTerms =
      ( \ast ->
          F.foldl'
            UPLC.applyTerm
            (unsafeFromRight @PLC.FreeVariableError $ UPLC.deBruijnTerm ast)
            args
      )
        <$> allASTs trace

data Algorithm
  = Bt
  | Bm
  | Bjbt1
  | Bjbt2
  | Fc
Tx.makeLift ''Algorithm

testNQueens :: IO TestTree
testNQueens = withTempFile $ \actual -> pure $ goldenVsFile name golden actual $ do
  trace <- loadFrom $ name <.> "uplc"
  let costs =
        evalOptimizerTrace
          evalCtx
          trace
          [ snd $ lift PLC.latestVersion (5 :: Integer)
          , snd $ lift PLC.latestVersion Fc
          ]
  void . runCertifier $ mkCertifier trace name (ReportOutput actual) costs
  where
    name = "n-queens"
    golden = "test" </> "certifier-report" </> "golden" </> name <.> "golden.report"

tests :: IO TestTree
tests = testNQueens
