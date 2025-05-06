{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Test.Run.Code where

import Prelude

import Control.Lens.Operators ((^.))
import Data.Either (isRight)
import Data.Text (Text)
import PlutusCore.DeBruijn.Internal (NamedDeBruijn)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusTx.Code (CompiledCode, getPlc)
import UntypedPlutusCore (DefaultFun, DefaultUni, progTerm)
import UntypedPlutusCore.Evaluation.Machine.Cek (CekEvaluationException, CountingSt (..), counting,
                                                 logEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm, runCekDeBruijn)

data CodeResult = CodeResult
  { codeResult
      :: Either
           (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
           (NTerm DefaultUni DefaultFun ())
  , codeBudget :: ExBudget
  , codeTraces :: [Text]
  }

evaluateCompiledCode :: CompiledCode a -> CodeResult
evaluateCompiledCode code = CodeResult{..}
 where
  term = getPlc code ^. progTerm
  params = defaultCekParametersForTesting
  (codeResult, CountingSt codeBudget, codeTraces) =
    runCekDeBruijn params counting logEmitter term

evaluatesToError :: CompiledCode a -> Bool
evaluatesToError = not . evaluatesWithoutError

evaluatesWithoutError :: CompiledCode a -> Bool
evaluatesWithoutError code = isRight (codeResult (evaluateCompiledCode code))
