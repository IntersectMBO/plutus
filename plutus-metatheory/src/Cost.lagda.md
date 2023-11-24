
# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Function using (_∘_)
open import Data.Bool
open import Data.List using (List;foldr)
open import Data.Nat using (ℕ;_+_)
open import Data.Integer using (ℤ)
open import Data.Float using (Float;fromℕ;_÷_;_*_;_≤ᵇ_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe using (Maybe;just;nothing;fromMaybe;maybe)
open import Data.Product using (_×_;_,_)
open import Data.String using (String;_++_;tail;padLeft;padRight)
open import Algebra using (IsMonoid)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;isEquivalence;cong₂)

open import Utils.Reflection using (defDec;defShow;defListConstructors)

open import Relation.Binary using (StrictTotalOrder)
open import Data.Char using (_≈ᵇ_)
open import Data.String
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as AVL using (Map;empty;unionWith;singleton) renaming (lookup to lookupAVL)
open import Builtin using (Builtin;showBuiltin;builtinList)
``` 

## Execution Budget

We will represent costs with Naturals. In the implementation `SatInt` is used, (integers that don't overflow, but saturate). 
As long as the budget is less than the maxInt then the result should be the same.

```
CostingNat : Set 
CostingNat = ℕ

record ExBudget : Set where
  constructor mkExBudget 
  field
    ExCPU : CostingNat -- CPU usage
    ExMem : CostingNat -- Memory usage

open ExBudget
```

`ExBudget` is a Monoid.

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

We define one constructor for each possible type of node in a UPLC term.

```
data StepKind : Set where 
    BConst 
      BVar
      BLamAbs
      BApply
      BDelay
      BForce
      BBuiltin -- Cost of evaluating a Builtin AST node, not the function itself
      BConstr 
      BCase : StepKind
```

We define a show function for StepKinds

```
showStepKind' : StepKind → String 
unquoteDef showStepKind' = defShow (quote StepKind) showStepKind' 

showStepKind : StepKind → String 
showStepKind s = fromMaybe "" (tail (showStepKind' s))   
```

and a list of constructors names

``` 
stepKindList : List StepKind
unquoteDef stepKindList = defListConstructors (quote StepKind) stepKindList 
``` 


```
data ExBudgetCategory : Set where
    BStep       : StepKind → ExBudgetCategory
    BBuiltinApp : Builtin → ExBudgetCategory  -- Cost of evaluating a fully applied builtin function
    BStartup    : ExBudgetCategory
```

## Machine Parameters

The CEK machine is parameterised by the following machine parameters.

```
record MachineParameters (A : Set) : Set where
    field 
      startupCost : A 
      cekMachineCost : ExBudgetCategory → A
      ε : A
      _∙_ : A → A → A
      costMonoid : IsMonoid _≡_ _∙_ ε
```

## Builtin Cost Model 

TODO

```
builtinCost : Builtin → ExBudget
--builtinCost _ = ε€ --TODO implement builtin costs
builtinCost _ = mkExBudget 1 0

```

## Default Machine Parameters

The default machine parameters for `ExBudget`.

TODO : For now we will define fixed costs. Later, we should implement getting these values from the cekMachineCosts.json file.
Probably, we will do this by reusing Haskell code.
 
```


defaultCekMachineCost : StepKind → ExBudget
defaultCekMachineCost s = mkExBudget 23000 100

defaultCekStartupCost : ExBudget 
defaultCekStartupCost = mkExBudget 100 100

 
exBudgetCategoryCost : ExBudgetCategory → ExBudget 
exBudgetCategoryCost (BStep x) = defaultCekMachineCost x
exBudgetCategoryCost (BBuiltinApp b) = builtinCost b
exBudgetCategoryCost BStartup = defaultCekStartupCost


defaultMachineParameters : MachineParameters ExBudget
defaultMachineParameters = record {
    startupCost = defaultCekStartupCost 
  ; cekMachineCost = exBudgetCategoryCost 
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
 } 

countingReport : ExBudget → String 
countingReport (mkExBudget cpu mem) = "\nCPU budget:    " ++ showℕ cpu ++ "\nMemory budget: " ++ showℕ mem
```
 
 ## Tallying budget 


We need a map from `ExBudgetCategory` into `ExBudget`. 
It's not the most efficient, but the simplest thing to do is to transform `ExBudgetCategory` into a string.

```
mkKeyFromExBudgetCategory : ExBudgetCategory → String 
mkKeyFromExBudgetCategory (BStep x) = "0" ++ showStepKind x
mkKeyFromExBudgetCategory (BBuiltinApp x) = "1"++ showBuiltin x
mkKeyFromExBudgetCategory BStartup = "2"

TallyingBudget : Set 
TallyingBudget = Map ExBudget × ExBudget

lookup : Map ExBudget → ExBudgetCategory → ExBudget
lookup m k with lookupAVL (mkKeyFromExBudgetCategory k) m 
... | just x = x
... | nothing = ε€
```


```
-- record TallyingBudget : Set where
--   constructor mkTB
--   field
--    #Const   : ℕ
--    #Var     : ℕ
--    #LamAbs  : ℕ
--    #Apply   : ℕ
--    #Delay   : ℕ
--    #Force   : ℕ
--    #Builtin : ℕ
--    #Constr  : ℕ 
--    #Case    : ℕ
--    budget   : ExBudget

--unit of TallyingBudget 
εT : TallyingBudget
εT = empty , ε€

-- adding TallyingBudgets
_∙T_ : TallyingBudget → TallyingBudget → TallyingBudget
(m , x) ∙T (n , y) = unionWith u m n , x ∙€ y
   where u : ExBudget → Maybe (ExBudget) → ExBudget
         u x (just y) = x ∙€ y
         u x nothing = x

postulate TallyingBudget-assoc : Algebra.Associative _≡_ _∙T_
postulate Tallying-budget-identityʳ : Algebra.RightIdentity _≡_ εT _∙T_

isMonoidTallyingBudget : IsMonoid _≡_ _∙T_ εT
isMonoidTallyingBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = TallyingBudget-assoc } 
     ; identity = (λ x → refl) , Tallying-budget-identityʳ }


tallyingCekMachineCost : ExBudgetCategory → TallyingBudget
tallyingCekMachineCost k = let spent = exBudgetCategoryCost k in singleton (mkKeyFromExBudgetCategory k) spent , spent

tallyingMachineParameters : MachineParameters TallyingBudget
tallyingMachineParameters = record { 
        startupCost = tallyingCekMachineCost BStartup 
      ; cekMachineCost = tallyingCekMachineCost
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
      } 

open import Text.Printf

budgetToString : ExBudget → String 
budgetToString (mkExBudget cpu mem) = padLeft ' ' 15 (showℕ cpu) ++ "  " ++ (padLeft ' ' 15 (showℕ mem))

printStepCost : StepKind → ExBudget → String
printStepCost sk budget = padRight ' ' 10 (showStepKind sk) ++ " " ++ padLeft ' ' 20 (budgetToString budget) ++ "\n"

printStepReport : Map ExBudget → String 
printStepReport mp = foldr (λ s xs → printStepCost s (lookup mp (BStep s)) ++ xs) "" stepKindList -- stepKindList

printBuiltinCost : Builtin → ExBudget → String 
printBuiltinCost b (mkExBudget 0 0) = "" 
printBuiltinCost b budget = padRight ' ' 22 (showBuiltin b) ++ " " ++ budgetToString budget ++ "\n"

printBuiltinReport : Map ExBudget → String 
printBuiltinReport mp = foldr (λ b xs → printBuiltinCost b (lookup mp (BBuiltinApp b)) ++ xs) "" builtinList

formatTimePicoseconds : Float → String
formatTimePicoseconds t = if 1e12 ≤ᵇ t then  (printf "%f s" (t ÷ 1e12)) else
                          if 1e9 ≤ᵇ t then  (printf "%f ms" (t ÷ 1e9)) else
                          if 1e6 ≤ᵇ t then  (printf "%f μs" (t ÷ 1e6)) else
                          if 1e3 ≤ᵇ t then  (printf "%f ns" (t ÷ 1e3)) else
                           printf "%f ps" t

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
     -- We would like to be ble to print the following  number as "%4.2f" 
     -- but Agda's printf currently doesn't support it.
    ++ printf "Time spent executing builtins:  %f%%\n" (fromℕ 100 * (getCPU totalBuiltinCosts) ÷ (getCPU budget)) ++ "\n"
    ++ "\n"
    ++ "Total budget spent:    " ++ budgetToString budget ++ "\n"
    ++  "Predicted execution time: " ++ formatTimePicoseconds (getCPU budget)
  where 
    totalComputeCost totalBuiltinCosts : ExBudget 
    totalComputeCost = foldr (λ x acc → (lookup mp (BStep x)) ∙€ acc) ε€ stepKindList
    totalBuiltinCosts = foldr _∙€_ ε€ (Data.List.map (lookup mp ∘ BBuiltinApp) builtinList)

    getCPU : ExBudget → Float
    getCPU n = fromℕ (ExCPU n)                        

 ```

 