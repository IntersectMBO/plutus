
# Builtin Cost Models

```
module Cost.Model where 

```

# Imports

```
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_;_⊔_;_⊓_;_<ᵇ_;_≡ᵇ_)

open import Data.Vec using (Vec;[];_∷_;sum;foldr;lookup) 
open import Cost.Base 
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
