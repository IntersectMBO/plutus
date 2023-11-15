```
{-# OPTIONS --type-in-type #-}

open import Cost

module Untyped.CEKWithCost {Budget : Set}(machineParameters : MachineParameters Budget) where
```

## Imports

```
open import Data.Unit using (⊤;tt)
open import Data.Nat using (ℕ;zero;suc)
open import Data.List using (List;[];_∷_)
open import Data.Product using (_,_)

open import Untyped using (_⊢)
open _⊢
open import Utils using (Writer;_>>_;_>>=_;return;maybe;Either;inj₁;inj₂;RuntimeError;gasError)
open import RawU using (tmCon)

open import Untyped.CEK
```

## Cost Monad

We instantiate a Writer Monad with the operations from the machine parameters

```
open MachineParameters machineParameters renaming (ε to e)
open Utils.WriterMonad e _∙_ 

CekM : Set → Set
CekM = Writer Budget 

spend : StepKind → CekM ⊤
spend st = tell (cekMachineCost st)

```

## Step with costs

```
stepC : State → CekM State
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

stepC (ε ◅ v)                               = return (□ v)
stepC ((s , -· ρ u) ◅ v)                    = return ((s , (v ·-)) ; ρ ▻ u)
stepC ((s , -·v v) ◅ vf)                    = return ((s , vf ·-) ◅ v)
stepC ((s , (V-ƛ ρ t ·-)) ◅ v)              = return (s ; ρ ∷ v ▻ t)
stepC ((s , (V-con _ _   ·-)) ◅ v)          = return ◆ -- constant in function position
stepC ((s , (V-delay _ _ ·-)) ◅ v)          = return ◆ -- delay in function position
stepC ((s , (V-IΠ b bapp ·-)) ◅ v)          = return ◆ -- delayed builtin in function position
stepC ((s , (V-constr i vs ·-)) ◅ v)        = return ◆ -- SOP in function position
stepC ((s , force-) ◅ V-IΠ b bapp)          = return (s ◅ V-I b (app⋆ bapp))
stepC ((s , force-) ◅ V-delay ρ t)          = stepC (s ; ρ ▻ t)
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
stepC ((s , case- ρ ts) ◅ V-IΠ _ _)         = return ◆ -- case of delqyed builtin
stepC ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ v) = do 
          -- spend cost of executing builtin function
          return (s ; [] ▻ BUILTIN' b (app bapp v))
stepC ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ v) = return (s ◅ V-I b (app bapp v))

stepC (□ v)               = return (□ v)
stepC ◆                   = return ◆

stepCperC : ℕ → (s : State) → CekM (Either RuntimeError State)
stepCperC 0       s = return (inj₁ gasError)
stepCperC (suc n) s = do
       s' ← stepC s 
       go s'
    where
       go : (t : State) → CekM (Either RuntimeError State)
       go (□ v) = return (inj₂ (□ v))
       go ◆     = return (inj₂ ◆)
       go s'    = stepCperC n s'
```
