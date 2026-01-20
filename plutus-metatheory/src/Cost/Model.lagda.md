---
title: Cost.Model
layout: page
---
# Builtin Cost Models

```
module Cost.Model where

```

# Imports

```
open import Agda.Builtin.Int using (Int;pos)
open import Data.Bool using (true;false;if_then_else_;not)
open import Data.Fin using (Fin;zero;suc)
open import Data.Maybe using (Maybe;just;nothing) renaming (map to mapMaybe)
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_;_⊔_;_⊓_;_<ᵇ_;_≡ᵇ_)
open import Data.Nat.DivMod using (_/_)
open import Data.List using ([];_∷_)
import Data.List as L
open import Data.Product using (Σ;_,_)
open import Data.String using (_==_)
open import Relation.Nullary using (_because_;ofʸ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Utils using (List;_×_;[];_∷_;_,_;length)
open import Data.Vec using (Vec;[];_∷_;sum;foldr;lookup;map)
open import Cost.Base
open import Cost.Raw renaming (mkLinearFunction to mkLF; mkTwoVariableLinearFunction to mkLF2;
  mkOneVariableQuadraticFunction to mkQF1; mkTwoVariableQuadraticFunction to mkQF2)
open import Cost.Size using () renaming (defaultValueMeasure to sizeOf)
open import Builtin using (Builtin;arity;builtinList;showBuiltin;decBuiltin)
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import Builtin.Constant.AtomicType using (AtomicTyCon;aInteger)
open import Untyped.CEK using (Value;V-con)
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
  quadraticCostIn1   : ∀{n} → Fin n → CostingNat → CostingNat → CostingNat → CostingModel n
  quadraticCostIn2   : ∀{n} → Fin n → Fin n → CostingNat → CostingNat → CostingNat → CostingNat
                            → CostingNat → CostingNat → CostingNat → CostingModel n
   -- take the cost literally if it is a positive integer, or else, use the provided model.
  literalCostIn      : ∀{n} → Fin n → CostingModel n → CostingModel n
  addedSizes         : ∀{n} → Intercept → Slope → CostingModel n
  multipliedSizes    : ∀{n} → Intercept → Slope → CostingModel n
  -- at least one argument
  minSize            : ∀{n} → Intercept → Slope → CostingModel (1 + n)
  maxSize            : ∀{n} → Intercept → Slope → CostingModel (1 + n)
   -- exactly two arguments
  twoArgumentsSubtractedSizes    : Intercept → Slope → CostingNat → CostingModel 2
  twoArgumentsConstAboveDiagonal : CostingNat → CostingModel 2 → CostingModel 2
  twoArgumentsConstBelowDiagonal : CostingNat → CostingModel 2 → CostingModel 2
  twoArgumentsConstOffDiagonal   : CostingNat → CostingModel 2 → CostingModel 2
  -- exactly 3 arguments
  twoArgumentsLinearInYAndZ      : Intercept → Slope → Slope → CostingModel 3
  twoArgumentsLinearInMaxYZ      : Intercept → Slope → CostingModel 3
  threeArgumentsExpModCost       : CostingNat → CostingNat → CostingNat -> CostingModel 3
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
runModel : ∀{n} → CostingModel n → Vec Value n → CostingNat
runModel (constantCost x) _ = x
runModel (linearCostIn n i s) xs = i + s * sizeOf (lookup xs n)
runModel (quadraticCostIn1 n c0 c1 c2) xs = let x = sizeOf (lookup xs n) in c0 + c1 * x + c2 * x * x
runModel (quadraticCostIn2 m n min c00 c10 c01 c20 c11 c02) xs =
  let x = sizeOf (lookup xs m)
      y = sizeOf (lookup xs n)
      r = c00 + c10 * x + c01 * y + c20 * x * x + c11 * x * y + c02 * y * y
  in min ⊔ r
runModel (addedSizes i s) xs = i + s * (sum (map sizeOf xs))
runModel (multipliedSizes i s) xs = i + s * (prod (map sizeOf xs))
runModel (minSize i s) xs = i + s * minimum (map sizeOf xs)
runModel (maxSize i s) xs = i + s * maximum (map sizeOf xs)
runModel (twoArgumentsLinearInYAndZ i s₁ s₂) (_ ∷ y ∷ z ∷ []) =
  let a = sizeOf y
      b = sizeOf z
  in i + s₁ * a + s₂ * b
runModel (twoArgumentsLinearInMaxYZ i s) (_ ∷ y ∷ z ∷ []) =
  let a = sizeOf y
      b = sizeOf z
  in i + s * maximum (a ∷ b ∷ [])
runModel (twoArgumentsSubtractedSizes i s min) (x ∷ y ∷ []) =
  let a = sizeOf x
      b = sizeOf y
  in i + s * (min ⊔ (a ∸ b))
runModel (twoArgumentsConstAboveDiagonal c m) (x ∷ y ∷ []) =
  let a = sizeOf x
      b = sizeOf y
  in if a <ᵇ b
      then c
      else runModel m (x ∷ y ∷ [])
runModel (twoArgumentsConstBelowDiagonal c m) (x ∷ y ∷ []) =
  let a = sizeOf x
      b = sizeOf y
  in if b <ᵇ a
      then c
      else runModel m (x ∷ y ∷ [])
runModel (twoArgumentsConstOffDiagonal c m) (x ∷ y ∷ []) =
  let a = sizeOf x
      b = sizeOf y
  in if not (a ≡ᵇ b)
      then c
      else runModel m (x ∷ y ∷ [])
runModel (threeArgumentsExpModCost c00 c11 c12) (x ∷ y ∷ z ∷ []) =
  let aa = sizeOf x
      ee = sizeOf y
      mm = sizeOf z
      cost0 = c00 + c11 * ee * mm + c12 * ee * mm * mm
  in if mm <ᵇ aa
     then cost0 + (cost0 / 2)
     else cost0

  -- ^ THIS IS INCOMPLETE: the real costing function branches if a > 5*c; however we measure
  -- sizes in bytes instead of words for expModInteger, so it gives incorrect results anyway.
runModel (literalCostIn n m) xs with lookup xs n
... | V-con (atomic aInteger) (pos (suc n)) = (n / 8) + 1
  --only uses the literal size if positive integer.
... | _ = runModel m xs
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
convertRawModel {suc n} (LinearInX (mkLF intercept slope)) = just (linearCostIn zero intercept slope)
convertRawModel {suc (suc n)} (LinearInY (mkLF intercept slope)) = just (linearCostIn (suc zero) intercept slope)
convertRawModel {3} (LinearInYAndZ (mkLF2 intercept slope1 slope2)) =
                   just (twoArgumentsLinearInYAndZ intercept slope1 slope2)
convertRawModel {3} (LinearInMaxYZ (mkLF intercept slope)) = just (twoArgumentsLinearInMaxYZ intercept slope)
convertRawModel {suc (suc n)} (QuadraticInX (mkQF1 c0 c1 c2)) = just (quadraticCostIn1 zero c0 c1 c2)
convertRawModel {suc (suc n)} (QuadraticInY (mkQF1 c0 c1 c2)) = just (quadraticCostIn1 (suc zero) c0 c1 c2)
convertRawModel {suc (suc (suc n))}(LinearInZ (mkLF intercept slope)) = just (linearCostIn (suc (suc zero)) intercept slope)
convertRawModel {suc (suc (suc n))} (QuadraticInZ (mkQF1 c0 c1 c2)) = just (quadraticCostIn1 (suc (suc zero)) c0 c1 c2)
convertRawModel {suc (suc n)} (QuadraticInXAndY (mkQF2 minVal c00 c10 c01 c20 c11 c02)) =
    just (quadraticCostIn2 zero (suc zero) minVal c00 c10 c01 c20 c11 c02)
convertRawModel {suc (suc (suc n))} (LiteralInYOrLinearInZ (mkLF intercept slope)) =
    just (literalCostIn  (suc zero) (linearCostIn (suc (suc zero)) intercept slope))
convertRawModel {2} (SubtractedSizes (mkLF intercept slope) c) = just (twoArgumentsSubtractedSizes intercept slope c)
convertRawModel {2} (ConstAboveDiagonal c m) = mapMaybe (twoArgumentsConstAboveDiagonal c) (convertRawModel m)
convertRawModel {2} (ConstBelowDiagonal c m) = mapMaybe (twoArgumentsConstBelowDiagonal c) (convertRawModel m)
convertRawModel {2} (ConstOffDiagonal c m) = mapMaybe (twoArgumentsConstOffDiagonal c) (convertRawModel m)
convertRawModel {3} (ExpModCost (mkExpModCostingFunction c00 c11 c12)) = just (threeArgumentsExpModCost c00 c11 c12)
convertRawModel _ = nothing

convertCpuAndMemoryModel : ∀{n} → CpuAndMemoryModel → Maybe (BuiltinModel n)
convertCpuAndMemoryModel (mkCpuAndMemoryModel cpuModel memoryModel) with convertRawModel cpuModel | convertRawModel memoryModel
... | just cm | just mm = just (record { costingCPU = cm ; costingMem = mm })
... | _ | _ = nothing
```

## Creation of mapping function

Creates a function mapping builtins to their corresponding costing models,
starting from a `BuiltinCostMap`.

We need to construct a `BuiltinModel (arity b)` for each `b`, and this may fail if
the model in the map doesn't correspond to the arity.

```
getModel : Builtin → BuiltinCostMap → Maybe (Σ Builtin (λ b → (BuiltinModel (arity b))))
getModel b [] = nothing
getModel b ((bn , rm) ∷ xs) with showBuiltin b == bn
... | false = getModel b xs
... | true = mapMaybe (b ,_) (convertCpuAndMemoryModel rm)
```

Once we have a list of all the builtins and their corresponding model,
we need to turn this into a function.

However Agda doesn't know that we are providing a model for *every* constructor,
so we provide a `dummyModel` to answer in the `[]` case.

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
      in mapMaybe lookupModel maybeModelList
```
