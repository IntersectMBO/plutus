module Common where

import PlutusCore.Core (defaultVersion)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.Evaluation.Result (EvaluationResult)
import PlutusCore.Name (Name)
import Prelude
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (unsafeEvaluateCekNoEmit)

type UplcProg = UPLC.Program Name DefaultUni DefaultFun ()

termToProg :: UPLC.Term Name DefaultUni DefaultFun () -> UplcProg
termToProg = UPLC.Program () (defaultVersion ())

evalUplcProg :: UplcProg -> EvaluationResult UplcProg
evalUplcProg p =
    fmap
        termToProg
        (unsafeEvaluateCekNoEmit defaultCekParameters (UPLC._progTerm p))
