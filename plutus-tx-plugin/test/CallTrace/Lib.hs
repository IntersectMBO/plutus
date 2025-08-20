{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module CallTrace.Lib where

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

import PlutusTx.Test (prettyBudget, prettyCodeSize)

goldenEvalCekTraceWithEmitter
  :: UPLC.EmitterMode UPLC.DefaultUni UPLC.DefaultFun
  -> TestName
  -> CompiledCode a
  -> TestNested
goldenEvalCekTraceWithEmitter emitter name compiledCode =
  nestedGoldenVsDocM name ".eval" $ ppCatch $ do
    uplc <- toUPlc compiledCode
    let
      UPLC.CekReport (UPLC.cekResultToEither -> evalRes) (UPLC.CountingSt budget) logOut =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.counting
          emitter
          (uplc ^. UPLC.progTerm)

      traceMsg =
        case logOut of
          [] -> ["No Trace Produced"]
          x  -> ["Trace:", vsep $ pretty <$> x]

    pure $ render @Text $ case evalRes of
      Left evalErr ->
        vsep
          [ prettyReadable evalErr
          , mempty
          , vsep traceMsg
          ]
      Right termRes ->
        vsep
          [ prettyBudget budget
          , prettyCodeSize compiledCode
          , mempty
          , vsep traceMsg
          , mempty
          , prettyPlcClassicSimple termRes
          ]
