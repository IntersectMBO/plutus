---
title: Cost.Raw
layout: page
---
# Raw Cost structures to inferface with Haskell

```
module Cost.Raw where
```

## Imports

```
open import Cost.Base using (CostingNat)
open import Data.String
open import Utils
```

## Interface with Haskell Machine Parameters

```
{-# FOREIGN GHC import Data.SatInt (fromSatInt) #-}
{-# FOREIGN GHC import Data.Functor.Identity (Identity, runIdentity) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExBudget (ExBudget(..))  #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExMemory (ExCPU(..), ExMemory(..)) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekMachineCostsForTesting) #-}
{-# FOREIGN GHC import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCostsBase(..)) #-}

postulate HCekMachineCosts : Set
postulate HExBudget : Set

{-# COMPILE GHC HCekMachineCosts = type CekMachineCostsBase Identity #-}
{-# COMPILE GHC HExBudget = type ExBudget #-}

postulate getCekStartupCost : HCekMachineCosts →  HExBudget
postulate getCekVarCost     : HCekMachineCosts →  HExBudget
postulate getCekConstCost   : HCekMachineCosts →  HExBudget
postulate getCekLamCost     : HCekMachineCosts →  HExBudget
postulate getCekDelayCost   : HCekMachineCosts →  HExBudget
postulate getCekForceCost   : HCekMachineCosts →  HExBudget
postulate getCekApplyCost   : HCekMachineCosts →  HExBudget
postulate getCekBuiltinCost : HCekMachineCosts →  HExBudget
postulate getCekConstrCost  : HCekMachineCosts →  HExBudget
postulate getCekCaseCost    : HCekMachineCosts →  HExBudget

{-# COMPILE GHC getCekStartupCost = runIdentity . cekStartupCost  #-}
{-# COMPILE GHC getCekVarCost     = runIdentity . cekVarCost      #-}
{-# COMPILE GHC getCekConstCost   = runIdentity . cekConstCost    #-}
{-# COMPILE GHC getCekLamCost     = runIdentity . cekLamCost      #-}
{-# COMPILE GHC getCekDelayCost   = runIdentity . cekDelayCost    #-}
{-# COMPILE GHC getCekForceCost   = runIdentity . cekForceCost    #-}
{-# COMPILE GHC getCekApplyCost   = runIdentity . cekApplyCost    #-}
{-# COMPILE GHC getCekBuiltinCost = runIdentity . cekBuiltinCost  #-}
{-# COMPILE GHC getCekConstrCost  = runIdentity . cekConstrCost   #-}
{-# COMPILE GHC getCekCaseCost    = runIdentity . cekCaseCost     #-}

postulate getCPUCost : HExBudget → CostingNat
postulate getMemoryCost : HExBudget → CostingNat

{-# COMPILE GHC getCPUCost = fromSatInt . (\(ExCPU x) -> x) . exBudgetCPU  #-}
{-# COMPILE GHC getMemoryCost = fromSatInt . (\(ExMemory x) -> x) . exBudgetMemory  #-}

-- postulate defaultHCekMachineCosts : HCekMachineCosts

-- {-# COMPILE GHC defaultHCekMachineCosts = defaultCekMachineCostsForTesting #-}
```

## Interface with Builtin model from JSON

```
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON  #-}

record LinearFunction : Set where
    constructor mkLinearFunction
    field
        intercept : CostingNat
        slope : CostingNat

{-# COMPILE GHC LinearFunction = data LinearFunction(LinearFunction) #-}

record QuadraticFunction : Set where
    constructor mkQuadraticFunction
    field
        coeff0 : CostingNat
        coeff1 : CostingNat
        coeff2 : CostingNat

{-# COMPILE GHC QuadraticFunction = data QuadraticFunction(QuadraticFunction) #-}

data RawModel : Set where
    ConstantCost          : CostingNat → RawModel
    AddedSizes            : LinearFunction → RawModel
    MultipliedSizes       : LinearFunction → RawModel
    MinSize               : LinearFunction → RawModel
    MaxSize               : LinearFunction → RawModel
    LinearInX             : LinearFunction → RawModel
    LinearInY             : LinearFunction → RawModel
    LinearInZ             : LinearFunction → RawModel
    LiteralInYOrLinearInZ : LinearFunction → RawModel
    QuadraticInY          : QuadraticFunction → RawModel
    QuadraticInZ          : QuadraticFunction → RawModel
    SubtractedSizes       : LinearFunction → CostingNat → RawModel
    ConstAboveDiagonal    : CostingNat → RawModel → RawModel
    ConstBelowDiagonal    : CostingNat → RawModel → RawModel
    ConstOffDiagonal      : CostingNat → RawModel → RawModel

{-# COMPILE GHC RawModel = data Model (ConstantCost | AddedSizes | MultipliedSizes |
                                   MinSize | MaxSize | LinearInX | LinearInY | LinearInZ |
                                   LiteralInYOrLinearInZ | QuadraticInY | QuadraticInZ |
                                   SubtractedSizes | ConstAboveDiagonal | ConstBelowDiagonal |
                                   ConstOffDiagonal)  #-}

record CpuAndMemoryModel : Set where
     constructor mkCpuAndMemoryModel
     field
        cpuModel : RawModel
        memoryModel : RawModel

{-# COMPILE GHC CpuAndMemoryModel = data CpuAndMemoryModel (CpuAndMemoryModel) #-}

BuiltinCostMap : Set
BuiltinCostMap = List (String × CpuAndMemoryModel)
```

```
RawCostModel : Set
RawCostModel = HCekMachineCosts × BuiltinCostMap
```
