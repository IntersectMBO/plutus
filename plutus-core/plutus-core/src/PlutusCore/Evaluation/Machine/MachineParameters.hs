{-# LANGUAGE StrictData    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Evaluation.Machine.MachineParameters
where

import           PlutusCore.Constant

import           PlutusCore.Core.Type                           hiding (Type)
import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.ExBudget         ()

import           GHC.Types                                      (Type)

{-| We need to account for the costs of evaluator steps and also built-in function
   evaluation.  The models for these have different structures and are used in
   different parts of the code, so inside the valuator we pass separate objects
   about most of the time .  It's convenient for clients of the evaluator to
   only have to worry about a single object, so the CostModel type bundles the
   two together.  We could conceivably have different evaluators with different
   internal costs, so we keep the machine costs abstract.  The model for Cek
   machine steps is in UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts.
-}
data CostModel machinecosts =
    CostModel {
      machineCostModel :: machinecosts
    , builtinCostModel :: BuiltinCostModel
    } deriving (Eq, Show)

{-| At execution time we need a 'BuiltinsRuntime' object which includes both the
  cost model for builtins and their denotations.  This bundles one of those
  together with the cost model for evaluator steps.  The 'term' type will be
  CekValue when we're using this with the CEK machine. -}
data MachineParameters machinecosts term (uni :: Type -> Type) (fun :: Type) =
    MachineParameters {
      machineCosts    :: machinecosts
    , builtinsRuntime :: BuiltinsRuntime fun (term uni fun)
    }

{-| This just uses 'toBuiltinsRuntime' function to convert a BuiltinCostModel to a BuiltinsRuntime. -}
toMachineParameters ::
    ( UniOf (val uni fun) ~ uni,
      -- In Cek.Internal we have `type instance UniOf (CekValue uni fun) = uni`, but we don't know that here.
      CostingPart uni  fun ~ BuiltinCostModel
    , HasConstant (val uni fun)
    , ToBuiltinMeaning uni fun
    )
    => CostModel machinecosts
    -> MachineParameters machinecosts val uni fun
toMachineParameters (CostModel mchnCosts builtinCosts) =
    MachineParameters mchnCosts (toBuiltinsRuntime builtinCosts)

