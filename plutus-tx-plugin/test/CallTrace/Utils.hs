{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module CallTrace.Utils where

import PlutusTx.Code

import Control.Lens ((^.))
import Data.Text (Text)
import Prettyprinter (vsep)
import Test.Tasty (TestName)

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Pretty (Pretty (pretty), Render (render), prettyPlcClassicSimple, prettyReadable)
import PlutusCore.Test (TestNested, ToUPlc (..), nestedGoldenVsDocM, ppCatch)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal qualified as UPLC

import PlutusTx.Test (prettyBudget)

goldenEvalCekTraceWithEmitter :: UPLC.EmitterMode UPLC.DefaultUni UPLC.DefaultFun -> TestName -> CompiledCode a -> TestNested
goldenEvalCekTraceWithEmitter emitter name compiledCode =
  nestedGoldenVsDocM name ".eval" $ ppCatch $ do
    uplc <- toUPlc compiledCode
    let
      (evalRes, UPLC.CountingSt budget, logOut) =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.counting
          emitter
          (uplc ^. UPLC.progTerm)
      termSize = UPLC.programSize uplc
      flatSize = UPLC.serialisedSize $ UPLC.UnrestrictedProgram uplc

      traceMsg =
        case logOut of
          [] -> ["Trace: <empty>"]
          x  -> [ "Trace:" , vsep $ pretty <$> x]

    case evalRes of
      Left evalErr ->
        pure $
          render @Text $
            vsep
              [ prettyReadable evalErr
              , mempty
              , vsep traceMsg
              ]
      Right termRes ->
        pure $
          render @Text $
            vsep
              [ prettyBudget budget termSize flatSize
              , mempty
              , vsep traceMsg
              , mempty
              , prettyPlcClassicSimple termRes
              ]
