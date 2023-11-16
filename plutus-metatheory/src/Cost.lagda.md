
# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Data.Nat using (ℕ;_+_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Product using (_×_;_,_)
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
```
 