# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Agda.Builtin.Unit using (tt)
open import Function using (_∘_)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat using (ℕ;zero;suc;_+_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Integer using (ℤ;∣_∣)
open import Data.Float using (Float;fromℕ;_÷_;_≤ᵇ_) renaming (show to show𝔽;_*_ to _*f_)
import Data.List as L

open import Data.Maybe using (Maybe;just;nothing;maybe′;fromMaybe) renaming (map to mapMaybe; _>>=_ to _>>=m_ )
open import Data.Product using () renaming (_,_ to _,,_)
open import Data.String using (String;_++_;padLeft;padRight;length)
open import Data.Vec using (Vec;replicate;[];_∷_;foldr)
open import Algebra using (IsMonoid)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;isEquivalence;cong₂)
open import Text.Printf using (printf)
open import Relation.Binary using (StrictTotalOrder)
open import Data.Char using (_≈ᵇ_)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as AVL 
          using (Map;empty;unionWith;singleton) 
          renaming (lookup to lookupAVL)

open import Utils using (_×_;_,_)
open import Builtin using (Builtin;showBuiltin;builtinList;arity)
open Builtin.Builtin
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon

open import Cost.Base
open import Cost.Size using (defaultValueMeasure)
open import Cost.Model
open import Cost.Raw
open import Untyped.CEK using (Value;V-con)
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

fromHExBudget : HExBudget → ExBudget 
fromHExBudget hb = mkExBudget (getCPUCost hb) (getMemoryCost hb)
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
     ; identity = (λ x → refl) ,, λ x → cong₂ mkExBudget (+-identityʳ (ExCPU x)) (+-identityʳ (ExMem x)) }
``` 

## Cost of executing a builtin

To calculate the cost of a builtin we obtain the corresponding builtin model, 
and run the cpu and memory model using the vector of argument sizes.

```
builtinCost : (b : Builtin) → BuiltinModel (arity b) → Vec Value (arity b) → ExBudget
builtinCost b bc cs = mkExBudget (runModel (costingCPU bc) cs) (runModel (costingMem bc) cs)
``` 


## Default Machine Parameters

The machine parameters for `ExBudget` for a given Cost Model

```
CostModel = HCekMachineCosts × ModelAssignment

cekMachineCostFunction : HCekMachineCosts → StepKind → ExBudget
cekMachineCostFunction mc BConst = fromHExBudget (getCekConstCost mc)
cekMachineCostFunction mc BVar = fromHExBudget (getCekVarCost mc)
cekMachineCostFunction mc BLamAbs = fromHExBudget (getCekLamCost mc)
cekMachineCostFunction mc BApply = fromHExBudget (getCekApplyCost mc)
cekMachineCostFunction mc BDelay = fromHExBudget (getCekDelayCost mc)
cekMachineCostFunction mc BForce = fromHExBudget (getCekForceCost mc)
cekMachineCostFunction mc BBuiltin = fromHExBudget (getCekBuiltinCost mc)
cekMachineCostFunction mc BConstr = fromHExBudget (getCekConstCost mc)
cekMachineCostFunction mc BCase = fromHExBudget (getCekCaseCost mc)

exBudgetCategoryCost : CostModel → ExBudgetCategory → ExBudget 
exBudgetCategoryCost (cekMc , _) (BStep x) = cekMachineCostFunction cekMc x
exBudgetCategoryCost (_ , ma) (BBuiltinApp b cs) = builtinCost b (ma b) cs
exBudgetCategoryCost (cekMc , _) BStartup = fromHExBudget (getCekStartupCost cekMc)

machineParameters : CostModel → MachineParameters ExBudget
machineParameters costmodel = record {
    cekMachineCost = exBudgetCategoryCost costmodel
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
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
(m , x) ∙T (n , y) = unionWith u m n , (x ∙€ y)
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
     ; identity = (λ x → refl) ,, Tallying-budget-identityʳ }

tallyingCekMachineCost : CostModel → ExBudgetCategory → TallyingBudget
tallyingCekMachineCost cm k = 
      let spent = exBudgetCategoryCost cm k 
      in singleton (mkKeyFromExBudgetCategory k) spent , spent

tallyingMachineParameters : CostModel → MachineParameters TallyingBudget
tallyingMachineParameters cm = record { 
        cekMachineCost = tallyingCekMachineCost cm
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
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
    totalBuiltinCosts = L.foldr _∙€_ ε€ (L.map (lookup mp ∘ (λ b → BBuiltinApp b (replicate (V-con (atomic aUnit) tt)))) builtinList)

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
        L.foldr (λ b xs → printBuiltinCost b (lookup mp (BBuiltinApp b (replicate (V-con (atomic aUnit) tt)))) ++ xs) 
              "" 
              builtinList     
    
    formatTimePicoseconds : Float → String
    formatTimePicoseconds t = if 1e12 ≤ᵇ t then (printf "%f s" (t ÷ 1e12)) else
                              if 1e9 ≤ᵇ t then  (printf "%f ms" (t ÷ 1e9)) else
                              if 1e6 ≤ᵇ t then  (printf "%f μs" (t ÷ 1e6)) else
                              if 1e3 ≤ᵇ t then  (printf "%f ns" (t ÷ 1e3)) else
                              printf "%f ps" t
 ```
