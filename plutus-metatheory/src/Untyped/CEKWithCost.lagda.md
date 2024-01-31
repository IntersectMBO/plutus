# CEK Machine with costs

This module implements a CEK machine for UPLC which computes costs.

```
open import Cost.Base

module Untyped.CEKWithCost {Budget : Set}(machineParameters : MachineParameters Budget) where
```

## Imports

```
open import Data.Unit using (⊤;tt)
open import Data.Nat using (ℕ;zero;suc)
open import Data.List using (List;[];_∷_)
open import Data.Vec using (Vec;[];_∷_;reverse)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym)

open import Untyped using (_⊢)
open _⊢
open import Utils using (Writer;_>>_;_>>=_;return;maybe;Either;inj₁;inj₂;RuntimeError;gasError;either;_∔_≣_)
open Writer
open import RawU using (tmCon)
open import Builtin using (Builtin;arity;signature)
open import Builtin.Signature using (fv;args♯)

open StepKind
open ExBudgetCategory

open import Untyped.CEK

```

## Cost Monad

We instantiate a Writer Monad with the operations from the machine parameters


```
open MachineParameters machineParameters renaming (ε to e)
open Utils.WriterMonad e _∙_

CekM : Set → Set
CekM = Writer Budget
```

### Spending operations

As opposed to the production implemention, our `spend` function does not implement slippage.
Slippage is an optimization that allows the interpreter to only add costs every n steps. 
Slippage is only semantically relevant in restricting mode (not currently implemented in agda), 
so we do not need to consider it here.

```
spend : StepKind → CekM ⊤
spend st = tell (cekMachineCost (BStep st))

spendStartupCost : CekM ⊤
spendStartupCost = tell startupCost
```

In order to calculate the cost of executing a builtin, we obtain a vector with 
the size of each constant argument using `extractArgSizes`. 

Non-constant argument should only occur in places where the builtin is polymorphic
and should be ignored by the cost model of the corresponding builtin. Therefore, 
they are added with a size of 0.

The function `extractArgSizes` get the arguments in inverse order, so we reverse 
them in the `spendBuiltin` function. 

```
extractConstants : ∀{b}
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → BApp b pt pa → Vec Value an
extractConstants base = []
extractConstants (app bapp v) = v ∷ extractConstants bapp
extractConstants (app⋆ bapp) = extractConstants bapp 

spendBuiltin : (b : Builtin) → fullyAppliedBuiltin b → CekM ⊤
spendBuiltin b bapp = tell (cekMachineCost (BBuiltinApp b argsizes))
     where argsizes = reverse (extractConstants bapp)
```

## Step with costs

Function `step` performs a single step in the CEK machine.

```
stepC : State → CekM State
-- computeCEK in the Haskell implementation
stepC (s ; ρ ▻ ` x)               = do
    spend BVar
    return (s ◅ lookup ρ x)
stepC (s ; ρ ▻ ƛ t)               = do
    spend BLamAbs
    return (s ◅ V-ƛ ρ t)
stepC (s ; ρ ▻ (t · u))           = do
    spend BApply
    return ((s , -· ρ u) ; ρ ▻ t)
stepC (s ; ρ ▻ force t)           = do
    spend BForce
    return ((s , force-) ; ρ ▻ t)
stepC (s ; ρ ▻ delay t)           = do 
    spend BDelay
    return (s ◅ V-delay ρ t)
stepC (s ; ρ ▻ con (tmCon t c))   = do 
    spend BConst
    return (s ◅ V-con t c)
stepC (s ; ρ ▻ constr i [])       = do
    spend BConstr    
    return (s ◅ V-constr i ε)
stepC (s ; ρ ▻ constr i (x ∷ xs)) = do 
    spend BConstr
    return ((s , constr- i ε ρ xs); ρ ▻ x)
stepC (s ; ρ ▻ case t ts)         = do 
    spend BCase
    return ((s , case- ρ ts) ; ρ ▻ t)
stepC (s ; ρ ▻ builtin b)         = do 
    spend BBuiltin
    return (s ◅ ival b)
stepC (s ; ρ ▻ error)             = return ◆

-- return∁EK in the Haskell implementation
stepC (ε ◅ v)                               = return (□ v)
stepC ((s , -· ρ u) ◅ v)                    = return ((s , (v ·-)) ; ρ ▻ u)
stepC ((s , -·v v) ◅ vf)                    = return ((s , vf ·-) ◅ v)
stepC ((s , (V-ƛ ρ t ·-)) ◅ v)              = return (s ; ρ ∷ v ▻ t)
stepC ((s , (V-con _ _   ·-)) ◅ v)          = return ◆ -- constant in function position
stepC ((s , (V-delay _ _ ·-)) ◅ v)          = return ◆ -- delay in function position
stepC ((s , (V-IΠ b bapp ·-)) ◅ v)          = return ◆ -- delayed builtin in function position
stepC ((s , (V-constr i vs ·-)) ◅ v)        = return ◆ -- SOP in function position
stepC ((s , force-) ◅ V-IΠ b bapp)          = return (s ◅ V-I b (app⋆ bapp))
stepC ((s , force-) ◅ V-delay ρ t)          = stepC (s ; ρ ▻ t) -- this recursive call could be inlined
                                                                -- in order to make evident that this is a single step 
                                                                -- but this would make the definition much longer.
stepC ((s , force-) ◅ V-ƛ _ _)              = return ◆ -- lambda in delay position
stepC ((s , force-) ◅ V-con _ _)            = return ◆ -- constant in delay position
stepC ((s , force-) ◅ V-I⇒ b bapp)          = return ◆ -- function in delay position
stepC ((s , force-) ◅ V-constr i vs)        = return ◆ -- SOP in delay position
stepC ((s , constr- i vs ρ []) ◅ v)         = return (s ◅ V-constr i (vs , v))
stepC ((s , constr- i vs ρ (x ∷ ts)) ◅ v)   = return ((s , constr- i (vs , v) ρ ts); ρ ▻ x)
stepC ((s , case- ρ ts) ◅ V-constr i vs)    = return (maybe (pushValueFrames s vs ; ρ ▻_) ◆ (lookup? i ts))
stepC ((s , case- ρ ts) ◅ V-ƛ _ _)          = return ◆ -- case of lambda
stepC ((s , case- ρ ts) ◅ V-con _ _)        = return ◆ -- case of constant
stepC ((s , case- ρ ts) ◅ V-delay _ _)      = return ◆ -- case of delay
stepC ((s , case- ρ ts) ◅ V-I⇒ _ _)         = return ◆ -- case of builtin value
stepC ((s , case- ρ ts) ◅ V-IΠ _ _)         = return ◆ -- case of delayed builtin
stepC ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ v) = do --fully applied builtin function
          let bapp' = mkFullyAppliedBuiltin (app bapp v) -- proof that b is fully applied
          spendBuiltin b bapp' 
          return (either (BUILTIN b bapp') (λ _ →  ◆) (s ◅_))
stepC ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ v) =  --partially applied builtin function
          return (s ◅ V-I b (app bapp v))

stepC (□ v)               = return (□ v)
stepC ◆                   = return ◆

stepperC-internal : ℕ → (s : State) → CekM (Either RuntimeError State)
stepperC-internal 0       s = return (inj₁ gasError)
stepperC-internal (suc n) s = do
       s' ← stepC s 
       go s'
    where
       go : (t : State) → CekM (Either RuntimeError State)
       go (□ v) = return (inj₂ (□ v))
       go ◆     = return (inj₂ ◆)
       go s'    = stepperC-internal n s'

stepperC : ℕ → (s : State) → CekM (Either RuntimeError State)
stepperC n s = do 
       spendStartupCost 
       stepperC-internal n s
```

## Proof of equivalence between CEK machine with and without costs

```
cekStepEquivalence : ∀ (s : State) → step s ≡ wrvalue (stepC s) 
cekStepEquivalence (s ; ρ ▻ ` _) = refl
cekStepEquivalence (s ; ρ ▻ ƛ _) = refl
cekStepEquivalence (s ; ρ ▻ (_ · _)) = refl
cekStepEquivalence (s ; ρ ▻ force _) = refl
cekStepEquivalence (s ; ρ ▻ delay _) = refl
cekStepEquivalence (s ; ρ ▻ con (tmCon _ _)) = refl
cekStepEquivalence (s ; ρ ▻ constr _ []) = refl
cekStepEquivalence (s ; ρ ▻ constr _ (_ ∷ _)) = refl
cekStepEquivalence (s ; ρ ▻ case _ _) = refl
cekStepEquivalence (s ; ρ ▻ builtin _) = refl
cekStepEquivalence (s ; ρ ▻ error) = refl
cekStepEquivalence (ε ◅ _) = refl
cekStepEquivalence ((s , -· _ _) ◅ _) = refl
cekStepEquivalence ((s , -·v _) ◅ _) = refl
cekStepEquivalence ((s , (V-ƛ _ _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , (V-con _ _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , (V-delay _ _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , (V-constr _ _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , (V-I⇒ b {am = zero} x ·-)) ◅ V) with BUILTIN' b (app x V)
... | inj₁ _ = refl
... | inj₂ _ = refl
cekStepEquivalence ((s , (V-I⇒ _ {am = suc _} _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , (V-IΠ _ _ ·-)) ◅ _) = refl
cekStepEquivalence ((s , force-) ◅ V-ƛ _ _) = refl
cekStepEquivalence ((s , force-) ◅ V-con _ _) = refl
cekStepEquivalence ((s , force-) ◅ V-delay ρ x) = cekStepEquivalence (s ; ρ ▻ x)
cekStepEquivalence ((s , force-) ◅ V-constr _ _) = refl
cekStepEquivalence ((s , force-) ◅ V-I⇒ _ _) = refl
cekStepEquivalence ((s , force-) ◅ V-IΠ _ _) = refl
cekStepEquivalence ((s , constr- _ _ _ []) ◅ _) = refl
cekStepEquivalence ((s , constr- _ _ _ (_ ∷ _)) ◅ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-ƛ _ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-con _ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-delay _ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-constr _ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-I⇒ _ _) = refl
cekStepEquivalence ((s , case- _ _) ◅ V-IΠ _ _) = refl
cekStepEquivalence (□ _) = refl
cekStepEquivalence ◆ = refl

cekStepperEquivalence : ∀ n s → stepper n s ≡ wrvalue (stepperC n s) 
cekStepperEquivalence zero s = refl 
cekStepperEquivalence (suc n) s rewrite sym (cekStepEquivalence s) with step s 
... | s ; ρ ▻ t = cekStepperEquivalence n (s ; ρ ▻ t)
... | s ◅ v = cekStepperEquivalence n  (s ◅ v)
... | □ x = refl
... | ◆ = refl
``` 