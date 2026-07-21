{-# LANGUAGE ScopedTypeVariables #-}

-- | A `UplcEvaluator` shared between the regular and steppable CEK machines.
module PlutusConformance.CekEvaluator (mkCekEvaluator) where

import PlutusConformance.Common
  ( EvaluationResult (..)
  , UplcEvaluator (..)
  )
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.MachineParameters qualified as UPLC
import PlutusCore.Evaluation.Machine.MachineParameters.Default (mkMachineVariantParametersFor)
import PlutusCore.Name.Unique (Name)
import PlutusPrelude (def)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
  ( CekEvaluationException
  , CekMachineCosts
  , CekValue
  , CountingSt (..)
  , ExBudgetMode
  , counting
  )

{-| Build a `UplcEvaluator` around a CEK-machine "run" function shaped like
`UntypedPlutusCore.Evaluation.Machine.Cek.runCekNoEmit`.  Both the regular CEK
machine and the steppable one
(`UntypedPlutusCore.Evaluation.Machine.SteppableCek.runCekNoEmit`) have
exactly this type -- the latter's haddock says it "provides the same
interface to the original CEK machine" -- so this is shared between the
`haskell-conformance` and `haskell-steppable-conformance` test suites rather
than being duplicated between them (as it was previously). -}
mkCekEvaluator
  :: ( UPLC.MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ())
       -> ExBudgetMode CountingSt DefaultUni DefaultFun
       -> UPLC.Term Name DefaultUni DefaultFun ()
       -> ( Either (CekEvaluationException Name DefaultUni DefaultFun) (UPLC.Term Name DefaultUni DefaultFun ())
          , CountingSt
          )
     )
  -> UplcEvaluator
mkCekEvaluator runCekNoEmit = UplcEvaluatorWithCosting $ \modelParams (UPLC.Program a v t) ->
  case mkMachineVariantParametersFor [def] modelParams of
    Left _ -> BadMachineParameters
    Right machParamsList ->
      case lookup def machParamsList of
        Nothing -> BadMachineParameters
        Just p ->
          let params = UPLC.MachineParameters def p
           in -- runCek-like functions (e.g. evaluateCekNoEmit) are partial on term's with
              -- free variables, that is why we manually check first for any free vars
              case UPLC.deBruijnTerm t of
                Left (_ :: UPLC.FreeVariableError) -> DecodeError -- For consistency with the flat decoder.
                Right _ ->
                  case runCekNoEmit params counting t of
                    (Left _, _) -> EvalFailure
                    (Right prog, CountingSt cost) -> EvalSuccess (UPLC.Program a v prog, cost)
