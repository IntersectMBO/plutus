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

data RawModel : Set where 
    ConstantCost       : CostingNat → RawModel 
    AddedSizes         : LinearFunction → RawModel 
    MultipliedSizes    : LinearFunction → RawModel
    MinSize            : LinearFunction → RawModel
    MaxSize            : LinearFunction → RawModel
    LinearCost         : LinearFunction → RawModel
    LinearInX          : LinearFunction → RawModel
    LinearInY          : LinearFunction → RawModel
    LinearInZ          : LinearFunction → RawModel
    SubtractedSizes    : LinearFunction → CostingNat → RawModel
    ConstAboveDiagonal : CostingNat → RawModel → RawModel
    ConstBelowDiagonal : CostingNat → RawModel → RawModel
    LinearOnDiagonal   : LinearFunction → CostingNat → RawModel

{-# COMPILE GHC RawModel = data Model (ConstantCost | AddedSizes | MultipliedSizes |
                                   MinSize | MaxSize | LinearCost | LinearInX | LinearInY |
                                   LinearInZ | SubtractedSizes | ConstAboveDiagonal |
                                   ConstBelowDiagonal | LinearOnDiagonal)  #-}

record CpuAndMemoryModel : Set where 
     constructor mkCpuAndMemoryModel 
     field 
        cpuModel : RawModel
        memoryModel : RawModel  

{-# COMPILE GHC CpuAndMemoryModel = data CpuAndMemoryModel (CpuAndMemoryModel) #-}         

BuiltinCostMap : Set                                
BuiltinCostMap = List (String × CpuAndMemoryModel)
```  