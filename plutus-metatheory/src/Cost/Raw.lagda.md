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

```
{-# FOREIGN GHC import Cost.JSON #-}

record LinearFunction : Set where
    constructor mkLinearFunction
    field 
        intercept : CostingNat 
        slope : CostingNat

{-# COMPILE GHC LinearFunction = data LinearFunction(LinearFunction) #-}

data Model : Set where 
    ConstantCost       : CostingNat → Model 
    AddedSizes         : LinearFunction → Model 
    MultipliedSizes    : LinearFunction → Model
    MinSize            : LinearFunction → Model
    MaxSize            : LinearFunction → Model
    LinearCost         : LinearFunction → Model
    LinearInX          : LinearFunction → Model
    LinearInY          : LinearFunction → Model
    LinearInZ          : LinearFunction → Model
    SubtractedSizes    : LinearFunction → CostingNat → Model
    ConstAboveDiagonal : CostingNat → Model → Model
    ConstBelowDiagonal : CostingNat → Model → Model
    LinearOnDiagonal   : LinearFunction → CostingNat → Model

{-# COMPILE GHC Model = data Model (ConstantCost | AddedSizes | MultipliedSizes |
                                   MinSize | MaxSize | LinearCost | LinearInX | LinearInY |
                                   LinearInZ | SubtractedSizes | ConstAboveDiagonal |
                                   ConstBelowDiagonal | LinearOnDiagonal)  #-}

record CpuAndMemoryModel : Set where 
     constructor mkCpuAndMemoryModel 
     field 
        cpuModel : Model
        memoryModel : Model  

{-# COMPILE GHC CpuAndMemoryModel = data CpuAndMemoryModel (CpuAndMemoryModel) #-}         

BuiltinCostMap : Set                                
BuiltinCostMap = List (String × CpuAndMemoryModel)
```  