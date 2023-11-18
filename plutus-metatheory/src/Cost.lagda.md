
# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Data.Nat using (ℕ;_+_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_;_,_)
open import Data.String using (String;_++_)
open import Algebra using (IsMonoid)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;isEquivalence;cong₂)
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

## Machine Parameters

The CEK machine is parameterised by the following machine parameters.

```
record MachineParameters (A : Set) : Set where
    field 
      startupCost : A 
      cekMachineCost : StepKind → A
      ε : A
      _∙_ : A → A → A
      costMonoid : IsMonoid _≡_ _∙_ ε
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

defaultMachineParameters : MachineParameters ExBudget
defaultMachineParameters = record {
    startupCost = defaultCekStartupCost 
  ; cekMachineCost = defaultCekMachineCost
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
 } 

countingReport : ExBudget → String 
countingReport (mkExBudget cpu mem) = "\nCPU budget:    " ++ showℕ cpu ++ "\nMemory budget: " ++ showℕ mem
```
 
 ## Tallying budget 

 ```
record TallyingBudget : Set where
  constructor mkTB
  field
   #Const   : ℕ
   #Var     : ℕ
   #LamAbs  : ℕ
   #Apply   : ℕ
   #Delay   : ℕ
   #Force   : ℕ
   #Builtin : ℕ
   #Constr  : ℕ 
   #Case    : ℕ
   budget   : ExBudget

--unit of TallyingBudget 
εT : TallyingBudget
εT = mkTB 0 0 0 0 0 0 0 0 0 ε€

-- adding TallyingBudgets
_∙T_ : TallyingBudget → TallyingBudget → TallyingBudget
mkTB a b c d e f g h i budget ∙T mkTB z y x w v u t s r budget' = 
   mkTB (a + z) (b + y) (c + x) (d + w) (e + v) (f + u) (g + t) (h + s) (i + r) (budget ∙€ budget')

postulate TallyingBudget-assoc : Algebra.Associative _≡_ _∙T_
postulate Tallying-budget-identityʳ : Algebra.RightIdentity _≡_ εT _∙T_

isMonoidTallyingBudget : IsMonoid _≡_ _∙T_ εT
isMonoidTallyingBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = TallyingBudget-assoc } 
     ; identity = (λ x → refl) , Tallying-budget-identityʳ }
  
tallyingCekMachineCost : StepKind → TallyingBudget
tallyingCekMachineCost BConst = record εT { #Const = 1 ; budget = defaultCekMachineCost BConst}
tallyingCekMachineCost BVar = record εT { #Var = 1 ; budget = defaultCekMachineCost BVar}
tallyingCekMachineCost BLamAbs = record εT { #LamAbs = 1 ; budget = defaultCekMachineCost BLamAbs}
tallyingCekMachineCost BApply = record εT { #Apply = 1 ; budget = defaultCekMachineCost BApply}
tallyingCekMachineCost BDelay = record εT { #Delay = 1 ; budget = defaultCekMachineCost BDelay}
tallyingCekMachineCost BForce = record εT { #Force = 1 ; budget = defaultCekMachineCost BForce}
tallyingCekMachineCost BBuiltin = record εT { #Builtin = 1 ; budget = defaultCekMachineCost BBuiltin}
tallyingCekMachineCost BConstr = record εT { #Constr = 1 ; budget = defaultCekMachineCost BConstr}
tallyingCekMachineCost BCase = record εT { #Case = 1 ; budget = defaultCekMachineCost BCase}

tallyingMachineParameters : MachineParameters TallyingBudget
tallyingMachineParameters = record { 
        startupCost = record εT { budget = defaultCekStartupCost }
      ; cekMachineCost = tallyingCekMachineCost
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
      } 

tallyingReport : TallyingBudget → String
tallyingReport (mkTB #Const #Var #LamAbs #Apply #Delay #Force #Builtin #Constr #Case budget) 
  =    countingReport budget ++ "\n\n"
    ++ "Const\t" ++ showℕ #Const ++ "\n"
    ++ "Var\t" ++ showℕ #Var ++ "\n"
    ++ "LamAbs\t" ++ showℕ #LamAbs ++ "\n"
    ++ "Apply\t" ++ showℕ #Apply ++ "\n"
    ++ "Delay\t" ++ showℕ #Delay ++ "\n"
    ++ "Force\t" ++ showℕ #Force ++ "\n"
    ++ "Builtin\t" ++ showℕ #Builtin ++ "\n"
    ++ "Constr\t" ++ showℕ #Constr ++ "\n"
    ++ "Case\t" ++ showℕ #Case ++ "\n"
    ++ "\n"

 ```