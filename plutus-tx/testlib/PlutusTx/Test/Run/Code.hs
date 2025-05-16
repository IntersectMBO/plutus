{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Test.Run.Code where

import Prelude

import Control.Lens.Operators ((^.))
import Data.Either (isRight)
import Data.SatInt (unSatInt)
import Data.Text (Text)
import Data.Text qualified as Text
import Formatting (commas, format)
import PlutusCore.DeBruijn.Internal (NamedDeBruijn)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Pretty
import PlutusTx qualified as Tx
import PlutusTx.Code (CompiledCode, getPlc)
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import Prettyprinter
import Test.Tasty.HUnit (Assertion, assertFailure)
import UntypedPlutusCore (DefaultFun, DefaultUni, progTerm)
import UntypedPlutusCore.Evaluation.Machine.Cek (CekEvaluationException, CountingSt (..), counting,
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

evaluateCompiledCode :: CompiledCode a -> EvalResult
evaluateCompiledCode code = EvalResult{..}
 where
  term = getPlc code ^. progTerm
  params = defaultCekParametersForTesting
  (evalResult, CountingSt evalResultBudget, evalResultTraces) =
    runCekDeBruijn params counting logEmitter term

evaluatesToError :: CompiledCode a -> Bool
evaluatesToError = not . evaluatesWithoutError

evaluatesWithoutError :: CompiledCode a -> Bool
evaluatesWithoutError code = isRight (evalResult (evaluateCompiledCode code))

{-| Evaluate 'CompiledCode' and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties.
-}
evaluationResultMatchesHaskell
  :: (Tx.Lift DefaultUni hask)
  => CompiledCode a
  -> (forall r. (Eq r, Show r) => r -> r -> k)
  -> hask
  -> k
evaluationResultMatchesHaskell actual =
  cekResultMatchesHaskellValue (compiledCodeToTerm actual)

--------------------------------------------------------------------------------
-- Assertions ------------------------------------------------------------------

assertEvaluatesSuccessfully :: CompiledCode a -> Assertion
assertEvaluatesSuccessfully code = do
  case evaluateCompiledCode code of
    EvalResult{evalResult = Right _} -> pure ()
    EvalResult{evalResult = Left err, evalResultTraces} ->
      assertFailure $
        Text.unpack $
          Text.unlines
            [ "Evaluation failed with an error:"
            , render (prettyPlcClassicSimple err)
            , "Evaluation traces:"
            , Text.unlines evalResultTraces
            ]

assertEvaluatesWithError :: CompiledCode a -> Assertion
assertEvaluatesWithError code = do
  case evaluateCompiledCode code of
    EvalResult{evalResult = Left _} -> pure ()
    EvalResult{evalResult = Right _, evalResultTraces} ->
      assertFailure $
        Text.unpack $
          Text.unlines
            [ "Evaluation succeeded, but expected an error."
            , "Evaluation traces:"
            , Text.unlines evalResultTraces
            ]

--------------------------------------------------------------------------------
-- Utilities -------------------------------------------------------------------

applyLifted
  :: (Tx.Lift DefaultUni a)
  => Tx.CompiledCode (a -> b) -> a -> Tx.CompiledCode b
applyLifted f a = Tx.unsafeApplyCode f (Tx.liftCodeDef a)
