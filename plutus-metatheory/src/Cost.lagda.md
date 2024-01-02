# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Function using (_∘_)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin;zero;suc)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_;_⊔_;_⊓_;_<ᵇ_;_≡ᵇ_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Integer using (ℤ;∣_∣)
open import Data.Float using (Float;fromℕ;_÷_;_≤ᵇ_) renaming (show to show𝔽;_*_ to _*f_)
import Data.List as L

open import Data.Maybe using (Maybe;just;nothing;maybe′;fromMaybe) renaming (map to mapMaybe; _>>=_ to _>>=m_ )
open import Data.Product using (_×_;_,_)
open import Data.String using (String;_++_;padLeft;padRight;length)
open import Data.Vec using (Vec;replicate;[];_∷_;sum;foldr) 
                     renaming (lookup to lookupVec)
open import Algebra using (IsMonoid)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;isEquivalence;cong₂)
open import Text.Printf using (printf)

open import Utils using (_,_;_∷_;[];DATA)
open DATA

open import Relation.Binary using (StrictTotalOrder)
open import Data.Char using (_≈ᵇ_)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as AVL 
          using (Map;empty;unionWith;singleton) 
          renaming (lookup to lookupAVL)
open import Builtin using (Builtin;showBuiltin;builtinList;lengthBS;arity)
open Builtin.Builtin
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import RawU using (TmCon) 
open TmCon
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon
open import Cost.Base 
``` 

## Execution Budget

An execution budget consist of two costs: CPU and memory costs.

```
record ExBudget : Set where
  constructor mkExBudget 
  field
    ExCPU : CostingNat -- CPU usage
    ExMem : CostingNat -- Memory usage

open ExBudget
```

The type for execution budget should be a Monoid.
We show that this is the case for `ExBudget`.

```
-- unit of the monoid
ε€ : ExBudget 
ε€ = mkExBudget 0 0 

-- binary operation
_∙€_ : ExBudget → ExBudget → ExBudget 
(mkExBudget xCPU xMem) ∙€ (mkExBudget yCPU yMem) = mkExBudget (xCPU + yCPU) (xMem + yMem)

-- Note: working with `Monoid` instances would imply working in Set₁, so we avoid it
-- and just state that `ExBudget` is a Monoid

isMonoidExBudget : IsMonoid _≡_ _∙€_ ε€
isMonoidExBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = λ x y z → cong₂ mkExBudget (+-assoc (ExCPU x) (ExCPU y) (ExCPU z)) 
                                                (+-assoc (ExMem x) (ExMem y) (ExMem z)) } 
     ; identity = (λ x → refl) , λ x → cong₂ mkExBudget (+-identityʳ (ExCPU x)) (+-identityʳ (ExMem x)) }
``` 

## Memory usage of type constants

For each type constant we calculate its size, as a measure of memory usage.

First we bring some functions from Haskell world.

```
postulate ℕtoWords : ℤ → CostingNat 
postulate g1ElementCost : CostingNat
postulate g2ElementCost : CostingNat
postulate mlResultElementCost : CostingNat 

{-# FOREIGN GHC {-# LANGUAGE MagicHash #-} #-}
{-# FOREIGN GHC import GHC.Exts (Int (I#)) #-}
{-# FOREIGN GHC import GHC.Integer  #-}
{-# FOREIGN GHC import GHC.Integer.Logarithms  #-}
{-# FOREIGN GHC import GHC.Prim #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G1 as BLS12_381.G1 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G2 as BLS12_381.G2 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.Pairing as BLS12_381.Pairing #-}

{-# COMPILE GHC  ℕtoWords = \i -> fromIntegral $ I# (integerLog2# (abs i) `quotInt#` integerToInt 64) + 1 #-}
{-# COMPILE GHC g1ElementCost = toInteger (BLS12_381.G1.memSizeBytes `div` 8) #-}
{-# COMPILE GHC g2ElementCost = toInteger (BLS12_381.G2.memSizeBytes `div` 8) #-}
{-# COMPILE GHC mlResultElementCost = toInteger (BLS12_381.Pairing.mlResultMemSizeBytes `div` 8) #-}
```

For each constant we return the corresponding size.

```
byteStringSize : Utils.ByteString → CostingNat 
byteStringSize x = let n = ∣ lengthBS x ∣ in ((n ∸ 1) / 8) + 1

defaultConstantMeasure : TmCon → CostingNat
defaultConstantMeasure (tmCon (atomic aInteger) x) = ℕtoWords x
defaultConstantMeasure (tmCon (atomic aBytestring) x) = byteStringSize x
defaultConstantMeasure (tmCon (atomic aString) x) = length x -- each Char costs 1
defaultConstantMeasure (tmCon (atomic aUnit) x) = 1
defaultConstantMeasure (tmCon (atomic aBool) x) = 1
defaultConstantMeasure (tmCon (atomic aData) (ConstrDATA _ [])) = 0
defaultConstantMeasure (tmCon (atomic aData) (ConstrDATA i (x ∷ xs))) = 
     defaultConstantMeasure (tmCon (atomic aData) x) 
   + defaultConstantMeasure (tmCon (atomic aData) (ConstrDATA i xs))
defaultConstantMeasure (tmCon (atomic aData) (MapDATA [])) = 0
defaultConstantMeasure (tmCon (atomic aData) (MapDATA ((x , y) ∷ xs))) =
     defaultConstantMeasure (tmCon (atomic aData) x) 
   + defaultConstantMeasure (tmCon (atomic aData) y) 
   + defaultConstantMeasure (tmCon (atomic aData) (MapDATA xs)) 
defaultConstantMeasure (tmCon (atomic aData) (ListDATA [])) = 0
defaultConstantMeasure (tmCon (atomic aData) (ListDATA (x ∷ xs))) =
     defaultConstantMeasure (tmCon (atomic aData) x) 
   + defaultConstantMeasure (tmCon (atomic aData) (ListDATA xs))
defaultConstantMeasure (tmCon (atomic aData) (iDATA x)) =  ℕtoWords x
defaultConstantMeasure (tmCon (atomic aData) (bDATA x)) = byteStringSize x
defaultConstantMeasure (tmCon (atomic aBls12-381-g1-element) x) = g1ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-g2-element) x) = g2ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-mlresult) x) = mlResultElementCost
defaultConstantMeasure (tmCon (list t) []) = 0
defaultConstantMeasure (tmCon (list t) (x ∷ xs)) = 
       defaultConstantMeasure (tmCon t x) 
     + defaultConstantMeasure (tmCon (list t) xs)
defaultConstantMeasure (tmCon (pair t u) (x , y)) = 
      1 + defaultConstantMeasure (tmCon t x) 
        + defaultConstantMeasure (tmCon u y)
```

## Builtin Cost Models

### Basic Definitions

```
Intercept : Set 
Intercept = CostingNat 

Slope : Set 
Slope = CostingNat 
```

### Models

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

```
data JSONCostingModel : Set where 
  constantCost       : CostingNat → JSONCostingModel
  linearCostInX      : Intercept → Slope → JSONCostingModel
  linearCostInY      : Intercept → Slope → JSONCostingModel
  linearCostInZ      : Intercept → Slope → JSONCostingModel
  addedSizes         : Intercept → Slope → JSONCostingModel
  multipliedSizes    : Intercept → Slope → JSONCostingModel
  minSize            : Intercept → Slope → JSONCostingModel
  maxSize            : Intercept → Slope → JSONCostingModel
  twoArgumentsLinearInXAndY      : Intercept → Slope → Slope → JSONCostingModel
  twoArgumentsSubtractedSizes    : Intercept → Slope → CostingNat → JSONCostingModel
  twoArgumentsLinearOnDiagonal   : CostingNat → Intercept → Slope → JSONCostingModel
  twoArgumentsConstAboveDiagonal : CostingNat → JSONCostingModel → JSONCostingModel
  twoArgumentsConstBelowDiagonal : CostingNat → JSONCostingModel → JSONCostingModel  

convertModel : ∀{n} → JSONCostingModel → Maybe (CostingModel n)
convertModel (constantCost c) = just (constantCost c)
convertModel {suc _} (linearCostInX i s) = just (linearCostIn zero i s)
convertModel {suc (suc _)} (linearCostInY i s) = just (linearCostIn (suc zero) i s)
convertModel {suc (suc (suc _))}(linearCostInZ i s) = just (linearCostIn (suc (suc zero)) i s)
convertModel (addedSizes i s) = just (addedSizes i s)
convertModel (multipliedSizes i s) = just (multipliedSizes i s)
convertModel {suc _} (minSize i s) = just (minSize i s)
convertModel {suc _} (maxSize i s) = just (maxSize i s)
convertModel {2} (twoArgumentsLinearInXAndY i s₁ s₂) = just (twoArgumentsLinearInXAndY i s₁ s₂)
convertModel {2} (twoArgumentsSubtractedSizes i s c) = just (twoArgumentsSubtractedSizes i s c)
convertModel {2} (twoArgumentsLinearOnDiagonal c i s) = just (twoArgumentsLinearOnDiagonal c i s)
convertModel {2} (twoArgumentsConstAboveDiagonal c m) = mapMaybe (twoArgumentsConstAboveDiagonal c) (convertModel m)
convertModel {2} (twoArgumentsConstBelowDiagonal c m) = mapMaybe (twoArgumentsConstBelowDiagonal c) (convertModel m)
convertModel _ = nothing

{-# FOREIGN GHC import Cost.JSON #-}

{-# COMPILE GHC JSONCostingModel = data CostingModel 
                (ConstantCost | LinearCostIn | AddedSizes 
                | MultipliedSizes | MinSize | MaxSize 
                | TwoArgumentsLinearInXAndY | TwoArgumentsSubtractedSizes 
                | TwoArgumentsLinearOnDiagonal 
                | TwoArgumentsConstAboveDiagonal 
                | TwoArgumentsConstBelowDiagonal )  #-}

postulate getJSONCostingModel : String → Maybe (JSONCostingModel × JSONCostingModel)
{-# COMPILE GHC getJSONCostingModel = getJSONCostingModel #-}

-- getJSONCostingModel : String → Maybe (JSONCostingModel × JSONCostingModel)
-- getJSONCostingModel _ = just (constantCost 42 , constantCost 1)
```

A model of a builtin consists of a pair of costing models, one for CPU and one for memory.

```
record BuiltinModel (ar : ℕ) : Set where 
    field 
        costingCPU costingMem : CostingModel ar
        
open BuiltinModel 

defaultBuiltinModel : ∀{n} → BuiltinModel n 
defaultBuiltinModel = record { costingCPU = constantCost 0 ; costingMem = constantCost 0 }
```

If there is an error in the JSON file (for example, assigning a `TwoArgumentsLinearInXAndY` model 
to a builtin which arity ≠ 2) we would like this error to be noticed at compile time.
Hence we write the assignment of the model to each builtin as a meta-program.

```
open import Agda.Builtin.Reflection using (Name;TC;Clause;clause;con;def;getDefinition;defineFun)
open import Reflection using (vArg;hArg;_>>=_)
open import Data.Unit using (⊤)
open import Utils.Reflection using (constructors)

getModel : ∀{n} → Builtin → BuiltinModel n 
getModel b with getJSONCostingModel (showBuiltin b) 
... | nothing = defaultBuiltinModel
... | just (cpu , mem) with convertModel cpu | convertModel mem 
... | just c | just m = record { costingCPU = c ; costingMem = m }
... | _ | _ = defaultBuiltinModel

createClauseforBuiltin : Name → Clause
createClauseforBuiltin bn = clause L.[] (vArg (con bn L.[]) L.∷ L.[]) 
                                (def (quote getModel) 
                                     (hArg (def (quote arity) (vArg (con bn L.[]) L.∷ L.[])) 
                                       L.∷ vArg (con bn L.[]) L.∷ L.[]))  

metaModelFromJSON :  (fun-name : Name) → TC ⊤ 
metaModelFromJSON nm = do 
         builtinDef ← getDefinition (quote Builtin)
         let clauseList = L.map createClauseforBuiltin (constructors builtinDef)
         defineFun nm clauseList

metaAssignModel : (b : Builtin) → BuiltinModel (arity b)
unquoteDef metaAssignModel = metaModelFromJSON metaAssignModel

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
runModel (linearCostIn n i s) xs = i + s * lookupVec xs n
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

### Cost of executing a builtin

To calculate the cost of a builtin we obtain the corresponding builtin model, 
and run the cpu and memory model using the vector of argument sizes.

```
builtinCost : (b : Builtin) → BuiltinModel (arity b) → Vec CostingNat (arity b) → ExBudget
builtinCost b bc cs = mkExBudget (runModel (costingCPU bc) cs) (runModel (costingMem bc) cs)
``` 

 For now, we define a static function to assign a model to the arithmetic builtins,
and `ifThenElse`.

TODO: Construct the assignment for all builtins from json file.

```
assignModel : (b : Builtin) → BuiltinModel (arity b)
assignModel addInteger = 
    record { costingCPU = maxSize 205665 812 
           ; costingMem = maxSize 1 1 }
assignModel subtractInteger = 
    record { costingCPU = maxSize 205665 812 
           ; costingMem = maxSize 1 1 }
assignModel multiplyInteger = 
    record { costingCPU = addedSizes 69522 11687 
           ; costingMem = addedSizes 0 1 }    
assignModel divideInteger =
    record { costingCPU = twoArgumentsConstAboveDiagonal 196500 (multipliedSizes 453240 220) 
           ; costingMem = twoArgumentsSubtractedSizes 0 1 1 }    
assignModel quotientInteger =
    record { costingCPU = twoArgumentsConstAboveDiagonal 196500 (multipliedSizes 453240 220) 
           ; costingMem = twoArgumentsSubtractedSizes 0 1 1 }    
assignModel remainderInteger =
    record { costingCPU = twoArgumentsConstAboveDiagonal 196500 (multipliedSizes 453240 220) 
           ; costingMem = twoArgumentsSubtractedSizes 0 1 1 }
assignModel modInteger =
    record { costingCPU = twoArgumentsConstAboveDiagonal 196500 (multipliedSizes 453240 220) 
           ; costingMem = twoArgumentsSubtractedSizes 0 1 1 }
assignModel equalsInteger =
    record { costingCPU = minSize 208512 421 
           ; costingMem = constantCost 1 }
assignModel lessThanInteger =
    record { costingCPU = minSize 208896 511 
           ; costingMem = constantCost 1 }
assignModel lessThanEqualsInteger =
    record { costingCPU = minSize 204924 473 
           ; costingMem = constantCost 1 }
assignModel ifThenElse = 
    record { costingCPU = constantCost 80556 
           ; costingMem = constantCost 1 }
assignModel appendByteString = 
    record { costingCPU = addedSizes 1000 571
           ; costingMem = addedSizes 0 1 }
assignModel appendString = 
    record { costingCPU = addedSizes 1000 24177
           ; costingMem = addedSizes 4 1 }
assignModel bData = 
    record { costingCPU = constantCost 1000 
           ; costingMem = constantCost 32 } 
assignModel consByteString = 
    record { costingCPU = linearCostIn (suc zero) 221973 511
           ; costingMem = addedSizes 0 1 } 
assignModel equalsByteString = 
    record { costingCPU = twoArgumentsLinearOnDiagonal 245000 216773 62
           ; costingMem = constantCost 1 } 
       
assignModel _ = --TODO rest of builtins (or rather implement constructing model from json)
    record { costingCPU = constantCost 0 
           ; costingMem = constantCost 0 }

``` 
## Default Machine Parameters

The default machine parameters for `ExBudget`.

TODO : For now we will define fixed costs. Later, we should 
implement getting these values from the `cekMachineCosts.json` file.
Probably, we will do this by reusing Haskell code.
 

-----------------------------------
Idea for generating records from datatypes
to facilitate the translation from/to JSON.

Given an enumeration datatype 
 
 data A = c1 a11 a22 | c2 a21 | ... | cn an1 an2 an3 

and a parameter prefix "param", I want to automatically construct from A, and 
 a type of payloads indexed by B : A → Set.
 1. A record recordA = { paramc1 : B c1; paramc2 : B c2 ; ... paramcn : B cn}  
 2. A function getParam : recordA → (a : A) → B a such that 
      getParam r c1 = r.paramc1 
      getParam r c2 = r.paramc2
      ... 
      getParam r cn = r.paramcn 

------------------------------------
```
defaultCekMachineCost : StepKind → ExBudget
defaultCekMachineCost _ = mkExBudget 23000 100

defaultCekStartupCost : ExBudget
defaultCekStartupCost = mkExBudget 100 100

exBudgetCategoryCost : ExBudgetCategory → ExBudget 
exBudgetCategoryCost (BStep x) = defaultCekMachineCost x
exBudgetCategoryCost (BBuiltinApp b cs) = builtinCost b (assignModel b) cs
exBudgetCategoryCost BStartup = defaultCekStartupCost

defaultMachineParameters : MachineParameters ExBudget
defaultMachineParameters = record {
    startupCost = defaultCekStartupCost 
  ; cekMachineCost = exBudgetCategoryCost 
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
  ; constantMeasure = defaultConstantMeasure 
 } 

countingReport : ExBudget → String 
countingReport (mkExBudget cpu mem) = 
      "\nCPU budget:    " ++ showℕ cpu 
   ++ "\nMemory budget: " ++ showℕ mem
```
 ## Tallying budget 

These functions define a type for Budgets that can record detailed cost information
about nodes and builtins.

We need a map from `ExBudgetCategory` into `ExBudget`. 
It's not the most efficient, but the simplest thing to do is to 
transform `ExBudgetCategory` into a string, and use that as keys.

```
mkKeyFromExBudgetCategory : ExBudgetCategory → String 
mkKeyFromExBudgetCategory (BStep x) = "0" ++ showStepKind x
mkKeyFromExBudgetCategory (BBuiltinApp x _) = "1"++ showBuiltin x
mkKeyFromExBudgetCategory BStartup = "2"

TallyingBudget : Set 
TallyingBudget = Map ExBudget × ExBudget

lookup : Map ExBudget → ExBudgetCategory → ExBudget
lookup m k with lookupAVL (mkKeyFromExBudgetCategory k) m 
... | just x = x
... | nothing = ε€
```

As required, `TallyingBudget` is a monoid. 

```
--unit of TallyingBudget 
εT : TallyingBudget
εT = empty , ε€

-- adding TallyingBudgets
_∙T_ : TallyingBudget → TallyingBudget → TallyingBudget
(m , x) ∙T (n , y) = unionWith u m n , x ∙€ y
   where u : ExBudget → Maybe (ExBudget) → ExBudget
         u x (just y) = x ∙€ y
         u x nothing = x

-- TODO : Prove these postulates.
postulate TallyingBudget-assoc : Algebra.Associative _≡_ _∙T_
postulate Tallying-budget-identityʳ : Algebra.RightIdentity _≡_ εT _∙T_

isMonoidTallyingBudget : IsMonoid _≡_ _∙T_ εT
isMonoidTallyingBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence 
                            ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = TallyingBudget-assoc } 
     ; identity = (λ x → refl) , Tallying-budget-identityʳ }

tallyingCekMachineCost : ExBudgetCategory → TallyingBudget
tallyingCekMachineCost k = 
      let spent = exBudgetCategoryCost k 
      in singleton (mkKeyFromExBudgetCategory k) spent , spent

tallyingMachineParameters : MachineParameters TallyingBudget
tallyingMachineParameters = record { 
        startupCost = tallyingCekMachineCost BStartup 
      ; cekMachineCost = tallyingCekMachineCost
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
      ; constantMeasure = defaultConstantMeasure
      } 

tallyingReport : TallyingBudget → String
tallyingReport (mp , budget) =  
       countingReport budget
    ++ "\n"
    ++ "\n"
    ++ printStepReport mp
    ++ "\n"
    ++ "startup    " ++ budgetToString (lookup mp BStartup) ++ "\n"
    ++ "compute    " ++ budgetToString totalComputeCost ++ "\n"
    -- ++ "AST nodes  " ++ ++ "\n"
    ++ "\n\n"
    ++ printBuiltinReport mp 
    ++ "\n" 
    ++ "Total builtin costs:   " ++ budgetToString totalBuiltinCosts ++ "\n"
     -- We would like to be able to print the following  number as "%4.2f" 
     -- but Agda's printf currently doesn't support it.
    ++ printf "Time spent executing builtins:  %f%%\n" (fromℕ 100 *f (getCPU totalBuiltinCosts) ÷ (getCPU budget)) ++ "\n"
    ++ "\n"
    ++ "Total budget spent:    " ++ budgetToString budget ++ "\n"
    ++  "Predicted execution time: " ++ formatTimePicoseconds (getCPU budget)
  where 
    totalComputeCost totalBuiltinCosts : ExBudget 
    totalComputeCost = L.foldr (λ x acc → (lookup mp (BStep x)) ∙€ acc) ε€ stepKindList
    totalBuiltinCosts = L.foldr _∙€_ ε€ (L.map (lookup mp ∘ (λ b → BBuiltinApp b (replicate 0))) builtinList)

    getCPU : ExBudget → Float
    getCPU n = fromℕ (ExCPU n)   

    budgetToString : ExBudget → String 
    budgetToString (mkExBudget cpu mem) = padLeft ' ' 15 (showℕ cpu) ++ "  " 
                                       ++ padLeft ' ' 15 (showℕ mem)

    printStepCost : StepKind → ExBudget → String
    printStepCost sk budget = padRight ' ' 10 (showStepKind sk) ++ " " 
                           ++ padLeft ' ' 20 (budgetToString budget) ++ "\n"

    printStepReport : Map ExBudget → String 
    printStepReport mp = L.foldr (λ s xs → printStepCost s (lookup mp (BStep s)) ++ xs)
                               "" 
                               stepKindList

    printBuiltinCost : Builtin → ExBudget → String 
    printBuiltinCost b (mkExBudget 0 0) = "" 
    printBuiltinCost b budget = padRight ' ' 22 (showBuiltin b) ++ " " 
                             ++ budgetToString budget ++ "\n"

    printBuiltinReport : Map ExBudget → String 
    printBuiltinReport mp = 
        L.foldr (λ b xs → printBuiltinCost b (lookup mp (BBuiltinApp b (replicate 0))) ++ xs) 
              "" 
              builtinList     
    
    formatTimePicoseconds : Float → String
    formatTimePicoseconds t = if 1e12 ≤ᵇ t then (printf "%f s" (t ÷ 1e12)) else
                              if 1e9 ≤ᵇ t then  (printf "%f ms" (t ÷ 1e9)) else
                              if 1e6 ≤ᵇ t then  (printf "%f μs" (t ÷ 1e6)) else
                              if 1e3 ≤ᵇ t then  (printf "%f ns" (t ÷ 1e3)) else
                              printf "%f ps" t
 ```
