{-# LANGUAGE StrictData    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Evaluation.Machine.MachineParameters
where

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



{-
data CostModel machinecosts uni fun =
    CostModel {
      machineCostModel :: machinecosts
    , builtinCostModel :: CostingPart uni fun
    }

deriving instance (Eq machinecosts, Eq (CostingPart uni fun)) =>
            Eq (CostModel machinecosts uni fun)
deriving instance (Show machinecosts, Show (CostingPart uni fun)) =>
            Show (CostModel machinecosts uni fun)
-}
