{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module PlutusIR.Transform.StrictLetRec.Tests.Lib where

import PlutusPrelude

import Control.Monad.Except
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Reader (runReaderT)
import Data.Text (Text)
import Data.Text.IO qualified as Text
import PlutusCore (Name, SrcSpan, latestVersion)
import PlutusCore.Compiler qualified as TPLC
import PlutusCore.Core qualified as TPLC
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error qualified as PLC
import PlutusCore.Evaluation.Machine.BuiltinCostModel (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
  ( defaultBuiltinCostModelForTesting
  , defaultCekMachineCostsForTesting
  )
import PlutusCore.Evaluation.Machine.MachineParameters
  ( CostModel (..)
  , MachineParameters (..)
  , mkMachineVariantParameters
  )
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)
import PlutusCore.Parser qualified as PC
import PlutusCore.Quote (runQuoteT)
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR.Compiler
  ( Provenance (..)
  , ccOpts
  , coPreserveLogging
  , noProvenance
  , toDefaultCompilationCtx
  )
import PlutusIR.Compiler qualified as PIR
import PlutusIR.Core qualified as PIR
import PlutusIR.Parser (pTerm)
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
  ( EvaluationResult (..)
  , evaluateCek
  , logEmitter
  , unsafeSplitStructuralOperational
  )
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts)

pirTermFromFile
  :: (MonadIO m, MonadFail m)
  => FilePath
  -> m (PIR.Term PIR.TyName PIR.Name DefaultUni DefaultFun SrcSpan)
pirTermFromFile file = do
  contents <- liftIO $ Text.readFile file
  PC.parseGen pTerm contents
    & runQuoteT
    & handlePirErrorByFailing @SrcSpan
    . modifyError (PIR.PLCError . PLC.ParseErrorE)

pirTermAsProgram :: PIR.Term tyname name uni fun () -> PIR.Program tyname name uni fun ()
pirTermAsProgram = PIR.Program () latestVersion

evalPirProgramWithTracesOrFail
  :: MonadFail m
  => PIR.Program PIR.TyName PIR.Name DefaultUni DefaultFun ()
  -> m (EvaluationResult (UPLC.Term Name DefaultUni DefaultFun ()), [Text])
evalPirProgramWithTracesOrFail pirProgram = do
  plcProgram <- compilePirProgramOrFail pirProgram
  evaluateUplcProgramWithTraces <$> compileTplcProgramOrFail plcProgram

compilePirProgramOrFail
  :: MonadFail m
  => PIR.Program PIR.TyName Name DefaultUni DefaultFun ()
  -> m (TPLC.Program PIR.TyName Name DefaultUni DefaultFun ())
compilePirProgramOrFail pirProgram = do
  ctx <- defaultCompilationCtx & handlePirErrorByFailing
  PIR.compileReadableToPlc (noProvenance <$ pirProgram)
    & flip runReaderT (set (ccOpts . coPreserveLogging) True ctx)
    & runQuoteT
    & runExceptT
    >>= \case
      Left (er :: PIR.Error DefaultUni DefaultFun (Provenance ())) -> fail $ show er
      Right p -> pure (void p)

compileTplcProgramOrFail
  :: MonadFail m
  => TPLC.Program PIR.TyName PIR.Name DefaultUni DefaultFun ()
  -> m (UPLC.Program Name DefaultUni DefaultFun ())
compileTplcProgramOrFail plcProgram =
  handlePirErrorByFailing @SrcSpan =<< do
    TPLC.compileProgram plcProgram
      & flip runReaderT TPLC.defaultCompilationOpts
      & runQuoteT
      & runExceptT

evaluateUplcProgramWithTraces
  :: UPLC.Program Name DefaultUni DefaultFun ()
  -> (EvaluationResult (UPLC.Term Name DefaultUni DefaultFun ()), [Text])
evaluateUplcProgramWithTraces uplcProg =
  first unsafeSplitStructuralOperational $
    evaluateCek logEmitter machineParameters (uplcProg ^. UPLC.progTerm)
  where
    costModel :: CostModel CekMachineCosts BuiltinCostModel
    costModel =
      CostModel defaultCekMachineCostsForTesting defaultBuiltinCostModelForTesting

    machineParameters :: DefaultMachineParameters
    machineParameters =
      MachineParameters def $ mkMachineVariantParameters def costModel

defaultCompilationCtx
  :: Either
       (PIR.Error DefaultUni DefaultFun (Provenance ()))
       (PIR.CompilationCtx DefaultUni DefaultFun a)
defaultCompilationCtx = do
  pirTcConfig <- modifyError (PIR.PLCError . PLC.TypeErrorE) $ PLC.getDefTypeCheckConfig noProvenance
  pure $ toDefaultCompilationCtx pirTcConfig

handlePirErrorByFailing
  :: (Pretty ann, MonadFail m) => Either (PIR.Error DefaultUni DefaultFun ann) a -> m a
handlePirErrorByFailing = \case
  Left e -> fail $ show e
  Right x -> pure x
