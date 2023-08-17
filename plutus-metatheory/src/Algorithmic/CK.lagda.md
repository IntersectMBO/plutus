# CK machine

```
module Algorithmic.CK where
```

## Imports

```
open import Data.Fin using (Fin)
open import Data.Vec as Vec using (Vec;[];_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;subst;cong)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Product renaming (_,_ to _,,_)

open import Utils using (Kind;*;_⇒_;Either;inj₁;RuntimeError;Monad)
open RuntimeError
open Monad {{...}}

open import Utils.List using (IBwd;[];_∷_;_:<_;_<><_;_<>>I_;start;bubble;no-empty-≣-<>>;lemma<>2;lem-≣-<>>)

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic using (Ctx;_⊢_;[];_∷_;lookupCase;bwdMkCaseType;lemma-bwdfwdfunction')
open Ctx
open _⊢_

open import Algorithmic.Signature using (_[_]SigTy)
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.ReductionEC using (Frame;Value;deval;ival;BUILTIN';V-I;VList;[];_[_]ᶠ) 
                                    renaming (step to app;step⋆ to app⋆)
open Frame
open Value

```

```
data Stack : (T : ∅ ⊢Nf⋆ *)(H : ∅ ⊢Nf⋆ *) → Set where
  ε   : {T : ∅ ⊢Nf⋆ *} → Stack T T
  _,_ : {T : ∅ ⊢Nf⋆ *}{H1 : ∅ ⊢Nf⋆ *}{H2 : ∅ ⊢Nf⋆ *}
    → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _▻_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → ∅ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → {t : ∅ ⊢ H} → Value t → State T
  □  : {t : ∅ ⊢ T} →  Value t → State T
  ◆   : (A : ∅ ⊢Nf⋆ *)  →  State T

-- Plugging a term into a stack yields a term again
closeStack : ∀{T H} → Stack T H → ∅ ⊢ H → ∅ ⊢ T
closeStack ε       t = t
closeStack (s , f) t = closeStack s ( f [ t ]ᶠ)

-- a state can be closed to yield a term again

closeState : ∀{T} → State T → ∅ ⊢ T
closeState (s ▻ t)           = closeStack s t
closeState (_◅_ s {t = t} v) = closeStack s t
closeState (□ {t = t} v)     = t
closeState (◆ A)             = error _

discharge : ∀{A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → Value t → ∅ ⊢ A
discharge {t = t} _ = t

pushValueFrames : ∀{T H BS XS} → Stack T H → {xs : IBwd (∅ ⊢_) BS} → VList xs → XS ≡ bwdMkCaseType BS H → Stack T XS
pushValueFrames s [] refl = s
pushValueFrames s (vs :< v) refl = pushValueFrames (s , -·v v) vs refl

step : ∀{A} → State A → State A
step (s ▻ ƛ L)                                = s ◅ V-ƛ L
step (s ▻ (L · M))                            = (s , -· M) ▻ L
step (s ▻ Λ L)                                = s ◅ V-Λ L
step (s ▻ (L ·⋆ A / refl))                    = (s , -·⋆ A) ▻ L
step (s ▻ wrap A B L)                         = (s , wrap-) ▻ L
step (s ▻ unwrap L refl)                      = (s , unwrap-) ▻ L
step (s ▻ con cn refl)                        = s ◅ V-con cn
step (s ▻ constr e A refl xs) with Vec.lookup A e in eq 
step (s ▻ constr e TSS refl []) | []          = s ◅ V-constr e TSS (sym eq) refl [] refl
step (s ▻ constr e TSS refl (x ∷ xs)) | _ ∷ _ = (s , constr- e TSS (sym eq) {tidx = start} [] xs) ▻ x
step (s ▻ case t ts)                          = (s , case- ts) ▻ t
step (s ▻ error A)                            = ◆ A
step (ε ◅ V)                                  = □ V
step ((s , (-· M)) ◅ V)                       = ((s , V ·-) ▻ M)
step ((s , -·v v) ◅ vf)                       = (s , vf ·-) ◅ v
step ((s , (V-ƛ t ·-)) ◅ V)                   = s ▻ (t [ discharge V ])
step ((s , (-·⋆ A)) ◅ V-Λ t)                  = s ▻ (t [ A ]⋆)
step ((s , wrap-) ◅ V)                        = s ◅ (V-wrap V)
step ((s , unwrap-) ◅ V-wrap V)               = s ▻ deval V
step ((s , constr- i TSS refl {tidx} vs ts) ◅ v) with Vec.lookup TSS i in eq 
... | []   with no-empty-≣-<>> tidx 
...      | () 
step ((s , constr- {n} {VS} {H} i TSS refl {tidx}{tvs} vs []) ◅ v) | _ ∷ _  = s ◅  
   V-constr i TSS
            (sym eq) 
            (trans (sym (lemma<>2 VS (H ∷ []))) (sym (cong ([] <><_) (lem-≣-<>> tidx))))
            {tvs :< deval v} 
            (vs :< v)
            refl
step ((s , constr- i TSS refl {r} vs (t ∷ ts)) ◅ v) | _ ∷ _ = 
      (s , constr- i TSS (sym eq) {bubble r} (vs :< v) ts) ▻ t
step ((s , case- cs) ◅ V-constr e TSS refl refl vs x) = pushValueFrames s vs (lemma-bwdfwdfunction' (Vec.lookup TSS e)) ▻ lookupCase e cs
step (s ▻ (builtin b / refl))                 = s ◅ ival b
step ((s , (V-I⇒ b {am = 0}     bt ·-)) ◅ vu) = s ▻ BUILTIN' b (app bt vu)
step ((s , (V-I⇒ b {am = suc _} bt ·-)) ◅ vu) = s ◅ V-I b (app bt vu)
step ((s , -·⋆ A) ◅ V-IΠ b {σA = σ} bt)       = s ◅ V-I b (app⋆ bt refl {σ [ A ]SigTy})
step (□ V)                                    = □ V
step (◆ A)                                    = ◆ A


 
stepper : ℕ → ∀{T}
  → State T
  → Either RuntimeError (State T)
stepper zero    st           = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

