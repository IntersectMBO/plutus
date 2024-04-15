
```
module Cost.Base where 

```

## Imports

```
open import Algebra using (IsMonoid)
open import Data.List using (List)
open import Data.Maybe using (Maybe;fromMaybe)
open import Data.Nat using (ℕ)
open import Data.String using (String;tail)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Utils.Reflection using (defDec;defShow;defListConstructors)
open import RawU using (TmCon)
open import Builtin using (Builtin;arity)
open import Untyped.CEK using (Value)
```

We will represent costs with Naturals. In the implementation `SatInt` is used, (integers that don't overflow, but saturate). 
As long as the budget is less than the maxInt then the result should be the same.

```
CostingNat : Set 
CostingNat = ℕ
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

## Recording expenditure

The following data structure is used to define the categories for which we
record expenditure.

```
data ExBudgetCategory : Set where
      -- Cost of Evaluating a machine step
    BStep       : StepKind → ExBudgetCategory

     -- Cost of evaluating a fully applied builtin function
    BBuiltinApp : (b : Builtin) → Vec Value (arity b) → ExBudgetCategory  

    -- Startup Cost
    BStartup    : ExBudgetCategory
```

## Machine Parameters

The CEK machine is parameterised by the following machine parameters.

```
record MachineParameters (Cost : Set) : Set where
    field
      cekMachineCost : ExBudgetCategory → Cost
      ε : Cost
      _∙_ : Cost → Cost → Cost
      costMonoid : IsMonoid _≡_ _∙_ ε

    startupCost : Cost 
    startupCost = cekMachineCost BStartup
``` 