{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}

module PlutusIR.Transform.StrictLetRec.Tests.Lib
  ( makeCompilationCtx
  , runCompilationM
  , parsePirProgram
  , evaluatePirFromFile
  ) where

import PlutusPrelude

import Control.Monad.Except (ExceptT, runExcept, runExceptT)
import Control.Monad.Identity (Identity)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT, runReaderT)
import Data.Text (Text)
import Data.Text.IO qualified as Text
import PlutusCore (Name)
import PlutusCore.Builtin (ToBuiltinMeaning (..))
import PlutusCore.Compiler qualified as TPLC
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error qualified as PCE
import PlutusCore.Evaluation.Machine.BuiltinCostModel (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel,
                                                          defaultCekMachineCosts)
import PlutusCore.Evaluation.Machine.MachineParameters (CostModel (..), MachineParameters (..),
                                                        mkMachineParameters)
import PlutusCore.Parser qualified as PC
import PlutusCore.Quote (QuoteT, runQuoteT)
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Analysis.Builtins (BuiltinsInfo)
import PlutusIR.Compiler (Provenance (Original), ccOpts, coPreserveLogging, noProvenance,
                          toDefaultCompilationCtx)
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core qualified as PIR
import PlutusIR.Test (pTermAsProg)
import PlutusIR.Transform.RewriteRules (RewriteRules)
import UntypedPlutusCore.Core.Type (_progTerm)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CekValue, EvaluationResult (..), logEmitter,
                                                 unsafeEvaluateCek)
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts)

makeCompilationCtx
  :: ( Default (CostingPart uni fun)
     , Default (BuiltinsInfo uni fun)
     , Default (RewriteRules uni fun)
     )
  => PLC.TypeCheckConfig uni fun
  -> PIR.CompilationCtx uni fun a
makeCompilationCtx pirTcConfig =
  toDefaultCompilationCtx pirTcConfig
    & set (ccOpts . coPreserveLogging) True

runCompilationM
  :: ReaderT
      (PIR.CompilationCtx DefaultUni DefaultFun ())
      (QuoteT (ExceptT (PIR.Error DefaultUni DefaultFun (Provenance ())) Identity))
      a
  -> a
runCompilationM m =
  unsafeFromRight @(PIR.Error DefaultUni DefaultFun (Provenance ())) . runExcept $
    runQuoteT do
      pirTcConfig <- PLC.getDefTypeCheckConfig noProvenance
      runReaderT m $ makeCompilationCtx pirTcConfig

parsePirProgram
  :: FilePath
  -> IO (PIR.Program PIR.TyName PIR.Name DefaultUni DefaultFun (Provenance ()))
parsePirProgram file = do
  res <- runExceptT @(PCE.Error DefaultUni DefaultFun ()) $ runQuoteT do
    contents <- liftIO $ Text.readFile file
    PC.parseGen pTermAsProg contents
  case res of
    Left err -> fail $ show err
    Right x  -> pure $ Original () <$ x

evaluatePirFromFile
  :: (MonadIO m, MonadFail m)
  => FilePath
  -> m (EvaluationResult (UPLC.Term Name DefaultUni DefaultFun ()), [Text])
evaluatePirFromFile fp = do
  program <- liftIO $ parsePirProgram fp

  pirTcConfig <-
    PLC.getDefTypeCheckConfig noProvenance
      & either (fail . show @(PCE.Error DefaultUni DefaultFun (Provenance ()))) pure

  plcProgram <-
    PIR.compileReadableToPlc program
      & flip runReaderT (makeCompilationCtx pirTcConfig)
      & runQuoteT
      & runExceptT
      >>= \case
        Left (er :: PIR.Error DefaultUni DefaultFun (Provenance ())) -> fail $ show er
        Right p -> pure p

  uplcTerm <- do
    TPLC.compileProgram plcProgram
      & flip runReaderT TPLC.defaultCompilationOpts
      & runQuoteT
      & runExceptT
      >>= \case
        Left (er :: PCE.Error DefaultUni DefaultFun (Provenance ())) -> fail $ show er
        Right UPLC.Program{_progTerm} -> pure _progTerm

  let costModel :: CostModel CekMachineCosts BuiltinCostModel =
        CostModel defaultCekMachineCosts defaultBuiltinCostModel

  let machineParameters
        :: MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ()) =
          mkMachineParameters def costModel

  pure $ unsafeEvaluateCek logEmitter machineParameters (void uplcTerm)
