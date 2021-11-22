{-# LANGUAGE StrictData    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Evaluation.Machine.MachineParameters
where

import PlutusCore.Constant

import PlutusCore.Core.Type hiding (Type)
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result

import Control.Monad.Except

{-| We need to account for the costs of evaluator steps and also built-in function
   evaluation.  The models for these have different structures and are used in
   different parts of the code, so inside the valuator we pass separate objects
   about most of the time .  It's convenient for clients of the evaluator to
   only have to worry about a single object, so the CostModel type bundles the
   two together.  We could conceivably have different evaluators with different
   internal costs, so we keep the machine costs abstract.  The model for Cek
   machine steps is in UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts.
-}
data CostModel machinecosts builtincosts =
    CostModel {
      machineCostModel :: machinecosts
    , builtinCostModel :: builtincosts
    } deriving (Eq, Show)

{-| At execution time we need a 'BuiltinsRuntime' object which includes both the
  cost model for builtins and their denotations.  This bundles one of those
  together with the cost model for evaluator steps.  The 'term' type will be
  CekValue when we're using this with the CEK machine. -}
data MachineParameters machinecosts fun m cause term =
    MachineParameters {
      machineCosts    :: machinecosts
    , builtinsRuntime :: BuiltinsRuntime' fun m cause term
    }

{-| This just uses 'toBuiltinsRuntime' function to convert a BuiltinCostModel to a BuiltinsRuntime. -}
toMachineParameters ::
    ( UniOf term ~ uni
      -- In Cek.Internal we have `type instance UniOf (CekValue uni fun) = uni`, but we don't know that here.
    , CostingPart uni fun ~ builtincosts
    , HasConstant term
    , ToBuiltinMeaning uni fun
    , MonadError (ErrorWithCause err cause) m
    , AsUnliftingError err, AsEvaluationFailure err
    )
    => CostModel machinecosts builtincosts
    -> MachineParameters machinecosts fun m cause term
toMachineParameters (CostModel mchnCosts builtinCosts) =
    MachineParameters mchnCosts (toBuiltinsRuntime' builtinCosts)
