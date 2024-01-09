
# Builtin Cost Models

```
module Cost.Model where 

```

# Imports

```
open import Data.Bool using (true;false;if_then_else_)
open import Data.Fin using (Fin;zero;suc)
open import Data.Maybe using (Maybe;just;nothing;map)
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_;_⊔_;_⊓_;_<ᵇ_;_≡ᵇ_)
open import Data.List using ([];_∷_)
import Data.List as L 
open import Data.Product using (Σ;_,_)
open import Data.String using (_==_)
open import Relation.Nullary using (_because_;ofʸ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Utils using (List;_×_;[];_∷_;_,_;length)
open import Data.Vec using (Vec;[];_∷_;sum;foldr;lookup) 
open import Cost.Base 
open import Cost.Raw renaming (mkLinearFunction to mkLF)
open import Builtin using (Builtin;arity;builtinList;showBuiltin;decBuiltin)
```

## Basic Definitions

```
Intercept : Set 
Intercept = CostingNat 

Slope : Set 
Slope = CostingNat 
```

## Models

A model is indexed by the number of arguments.

For example, for `ifThenElse` we would assign a model `constantCost : CostingModel 3`,
which is a model for a builtin that takes three arguments.

For `linearCost` the model takes an index indicating on which argument the cost
should be calculated.

``` 
data CostingModel : ℕ → Set where 
   -- Any number of arguments
  constantCost       : ∀{n} → CostingNat → CostingModel n
  linearCostIn       : ∀{n} → Fin n → Intercept → Slope → CostingModel n
  addedSizes         : ∀{n} → Intercept → Slope → CostingModel n 
  multipliedSizes    : ∀{n} → Intercept → Slope → CostingModel n
  -- at least one argument
  minSize            : ∀{n} → Intercept → Slope → CostingModel (1 + n)
  maxSize            : ∀{n} → Intercept → Slope → CostingModel (1 + n)
   -- exactly two arguments 
  twoArgumentsLinearInXAndY      : Intercept → Slope → Slope → CostingModel 2
  twoArgumentsSubtractedSizes    : Intercept → Slope → CostingNat → CostingModel 2
  twoArgumentsLinearOnDiagonal   : CostingNat → Intercept → Slope → CostingModel 2
  twoArgumentsConstAboveDiagonal : CostingNat → CostingModel 2 → CostingModel 2
  twoArgumentsConstBelowDiagonal : CostingNat → CostingModel 2 → CostingModel 2
``` 

A model of a builtin consists of a pair of costing models, one for CPU and one for memory.

```
record BuiltinModel (ar : ℕ) : Set where 
    field 
        costingCPU costingMem : CostingModel ar
        
open BuiltinModel public
```

### Model interpretations

Some helper functions.

```
prod : ∀ {n} → Vec ℕ n → ℕ
prod = foldr _ _*_ 1

maximum minimum : ∀ {n} → Vec ℕ (suc n) → ℕ
maximum (a ∷ xs) = foldr _ _⊔_ a xs
minimum (a ∷ xs) = foldr _ _⊓_ a xs
``` 

Given a model and the sizes of the arguments we can compute a cost.

```
runModel : ∀{n} → CostingModel n → Vec CostingNat n → CostingNat 
runModel (constantCost x) _ = x
runModel (linearCostIn n i s) xs = i + s * lookup xs n
runModel (addedSizes i s) xs = i + s * (sum xs)
runModel (multipliedSizes i s) xs = i + s * (prod xs)
runModel (minSize i s) xs = i + s * minimum xs
runModel (maxSize i s) xs = i + s * maximum xs
runModel (twoArgumentsLinearInXAndY i s₁ s₂) (a ∷ b ∷ []) = i + s₁ * a + s₂ * b 
runModel (twoArgumentsSubtractedSizes i s min) (a ∷ b ∷ []) = i + s * (min ⊔ (a ∸ b))
runModel (twoArgumentsLinearOnDiagonal c i s) (a ∷ b ∷ []) = 
    if a ≡ᵇ b 
      then i + s * a 
      else c
runModel (twoArgumentsConstAboveDiagonal c m) (a ∷ b ∷ []) = 
    if a <ᵇ b 
      then c 
      else runModel m (a ∷ b ∷ [])
runModel (twoArgumentsConstBelowDiagonal c m) (a ∷ b ∷ []) =
    if b <ᵇ a 
      then c 
      else runModel m (a ∷ b ∷ [])
```

## Convert from Raw Model

May fail if the model doesn't correspond to the number of arguments.

```
convertRawModel : ∀{n} → RawModel → Maybe (CostingModel n) 
convertRawModel (ConstantCost c) = just (constantCost c)
convertRawModel (AddedSizes (mkLF intercept slope)) = just (addedSizes intercept slope)
convertRawModel (MultipliedSizes (mkLF intercept slope)) = just (multipliedSizes intercept slope)
convertRawModel {suc n} (MinSize (mkLF intercept slope)) = just (minSize intercept slope)
convertRawModel {suc n} (MaxSize (mkLF intercept slope)) = just (maxSize intercept slope)
convertRawModel {suc n} (LinearCost (mkLF intercept slope)) = just (linearCostIn zero intercept slope)
convertRawModel {suc n} (LinearInX (mkLF intercept slope)) = just (linearCostIn zero intercept slope)
convertRawModel {suc (suc n)} (LinearInY (mkLF intercept slope)) = just (linearCostIn (suc zero) intercept slope)
convertRawModel {suc (suc (suc n))}(LinearInZ (mkLF intercept slope)) = just (linearCostIn (suc (suc zero)) intercept slope)
convertRawModel {2} (SubtractedSizes (mkLF intercept slope) c) = just (twoArgumentsSubtractedSizes intercept slope c)
convertRawModel {2} (ConstAboveDiagonal c m) = map (twoArgumentsConstAboveDiagonal c) (convertRawModel m)
convertRawModel {2} (ConstBelowDiagonal c m) = map (twoArgumentsConstBelowDiagonal c) (convertRawModel m)
convertRawModel {2} (LinearOnDiagonal (mkLF intercept slope) c) = just (twoArgumentsLinearOnDiagonal c intercept slope)
convertRawModel _ = nothing

convertCpuAndMemoryModel : ∀{n} → CpuAndMemoryModel → Maybe (BuiltinModel n)
convertCpuAndMemoryModel (mkCpuAndMemoryModel cpuModel memoryModel) with convertRawModel cpuModel | convertRawModel memoryModel 
... | just cm | just mm = just (record { costingCPU = cm ; costingMem = mm })
... | just _ | nothing = nothing
... | nothing | m = nothing
```

## Creation of mapping function 

Creates a function mapping builtins to their corresponding costing models, 
starting from a `BuiltinCostMap`.

We need to construct a `BuiltinModel (arity b)` for each `b`, and this may fail if
the model int the map doesn't correspond to the arity. 

```
getModel : Builtin → BuiltinCostMap → Maybe (Σ Builtin (λ b → (BuiltinModel (arity b))))
getModel b [] = nothing
getModel b ((bn , rm) ∷ xs) with showBuiltin b == bn 
... | false = getModel b xs
... | true = map (b ,_) (convertCpuAndMemoryModel rm)
``` 

Once we have a list of all the builtins and their corresponding model, 
we need to turn this into a function.  

However Agda doesn't know 
that we are providing a model for *every* constructor, so we 
provide a `dummyModel` to answer in the `[]` case.

``` 
dummyModel :  ∀{n} → BuiltinModel n 
dummyModel = record { costingCPU = constantCost 0 ; costingMem = constantCost 0 }

lookupModel : L.List (Σ Builtin (λ b → (BuiltinModel (arity b)))) → (b : Builtin) → BuiltinModel (arity b)
lookupModel [] _ = dummyModel  --should not happen if builtinList is complete
                                  --but Agda doesn't know this (we do).
lookupModel ((b , bm) ∷ xs) b' with decBuiltin b b'
... | false because p = lookupModel xs b'
... | true because ofʸ refl = bm

allJust : {A : Set} → (xs : L.List (Maybe A)) → Maybe (L.List A)
allJust [] = just []
allJust (just x ∷ xs) with allJust xs 
... | just xs' = just (x ∷ xs')
... | nothing = nothing
allJust (nothing ∷ xs) = nothing

ModelAssignment : Set 
ModelAssignment = (b : Builtin) → BuiltinModel (arity b)

createMap : BuiltinCostMap → Maybe ModelAssignment
createMap bmap = 
      let modelMaybeList = L.map (λ b → getModel b bmap) builtinList 
          maybeModelList = allJust modelMaybeList
      in map lookupModel maybeModelList
``` 