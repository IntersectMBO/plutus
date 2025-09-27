{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.Eval where

import Prelude

import Data.Either (isRight)
import Data.SatInt (unSatInt)
import Data.Text (Text)
import Formatting (commas, format)
import PlutusCore.DeBruijn.Internal (NamedDeBruijn)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)
import PlutusCore.Pretty
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import Prettyprinter (dot, indent, plural, vsep, (<+>))
import UntypedPlutusCore (DefaultFun, DefaultUni, Program (..))
import UntypedPlutusCore.Evaluation.Machine.Cek (CekEvaluationException, CekReport (..),
                                                 CountingSt (..), cekResultToEither, counting,
                                                 logEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm, runCekDeBruijn)

data EvalResult = EvalResult
  { evalResult
      :: Either
           (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
           (NTerm DefaultUni DefaultFun ())
  , evalResultBudget :: ExBudget
  , evalResultTraces :: [Text]
  }
  deriving stock (Show)

instance Pretty EvalResult where
  pretty EvalResult{..} =
    vsep
      [ case evalResult of
          Left err ->
            vsep
              [ "Evaluation FAILED:"
              , indent 2 $ prettyPlcClassicSimple err
              ]
          Right term ->
            vsep
              [ "Evaluation was SUCCESSFUL, result is:"
              , indent 2 $ prettyPlcReadableSimple term
              ]
      , mempty
      , vsep
          [ "Execution budget spent:"
          , indent 2 $ prettyExBudget evalResultBudget
          ]
      , mempty
      , if null evalResultTraces
          then "No traces were emitted"
          else
            vsep
              [ "Evaluation"
                  <+> plural "trace" "traces" (length evalResultTraces)
                  <> ":"
              , indent 2 $
                  vsep $
                    zipWith
                      (\idx trace -> pretty idx <> dot <+> pretty trace)
                      [1 :: Int ..]
                      evalResultTraces
              ]
      , mempty
      ]

displayEvalResult :: EvalResult -> Text
displayEvalResult = display

displayExBudget :: ExBudget -> Text
displayExBudget = render . prettyExBudget

prettyExBudget :: ExBudget -> Doc ann
prettyExBudget
  ExBudget{exBudgetCPU = ExCPU cpu, exBudgetMemory = ExMemory mem} =
    vsep
      [ "CPU" <+> pretty (format commas (unSatInt cpu))
      , "MEM" <+> pretty (format commas (unSatInt mem))
      ]

{-| Evaluates the given 'CompiledCode' using the CEK machine
with the default machine parameters.
-}
evaluateCompiledCode :: CompiledCode a -> EvalResult
evaluateCompiledCode = evaluateCompiledCode' defaultCekParametersForTesting

{-| Evaluates the given 'CompiledCode' using the CEK machine
with the given machine parameters.
-}
evaluateCompiledCode'
  :: DefaultMachineParameters DefaultFun -> CompiledCode a -> EvalResult
evaluateCompiledCode' params code = EvalResult{..}
 where
  Program _ann _version term = getPlcNoAnn code
  CekReport (cekResultToEither -> evalResult) (CountingSt evalResultBudget) evalResultTraces =
    runCekDeBruijn params counting logEmitter term

evaluatesToError :: CompiledCode a -> Bool
evaluatesToError = not . evaluatesWithoutError

evaluatesWithoutError :: CompiledCode a -> Bool
evaluatesWithoutError code = isRight (evalResult (evaluateCompiledCode code))
