# CK machine

```
module Algorithmic.CK where
```

## Imports

```
open import Data.List as L using (List;[];_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym)
open import Data.Nat using (ℕ;zero;suc)

open import Utils using (Kind;*;_⇒_;Either;inj₁;RuntimeError;Monad)
open RuntimeError
open Monad {{...}}

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic using (Ctx;_⊢_)
open Ctx
open _⊢_

open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.ReductionEC using (Frame;Value;deval;ival;BUILTIN';V-I) 
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

-- Plugging a term of suitable type into a frame yields a term again
closeFrame : ∀{T H} → Frame T H → ∅ ⊢ H → ∅ ⊢ T
closeFrame (-· u)          t = t · u
closeFrame (_·- {t = t} v) u = t · u
closeFrame (-·⋆ A)         t = t ·⋆ A / refl
closeFrame wrap-           t = wrap _ _ t
closeFrame unwrap-         t = unwrap t refl
-- Plugging a term into a stack yields a term again

closeStack : ∀{T H} → Stack T H → ∅ ⊢ H → ∅ ⊢ T
closeStack ε       t = t
closeStack (s , f) t = closeStack s (closeFrame f t)

-- a state can be closed to yield a term again

closeState : ∀{T} → State T → ∅ ⊢ T
closeState (s ▻ t)           = closeStack s t
closeState (_◅_ s {t = t} v) = closeStack s t
closeState (□ {t = t} v)     = t
closeState (◆ A)             = error _

discharge : ∀{A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → Value t → ∅ ⊢ A
discharge {t = t} _ = t

step : ∀{A} → State A → State A
step (s ▻ ƛ L)                    = s ◅ V-ƛ L
step (s ▻ (L · M))                = (s , -· M) ▻ L
step (s ▻ Λ L)                    = s ◅ V-Λ L
step (s ▻ (L ·⋆ A / refl))        = (s , -·⋆ A) ▻ L
step (s ▻ wrap A B L)             = (s , wrap-) ▻ L
step (s ▻ unwrap L refl)          = (s , unwrap-) ▻ L
step (s ▻ con cn)                 = s ◅ V-con cn
step (s ▻ error A)                = ◆ A
step (ε ◅ V)                      = □ V
step ((s , (-· M)) ◅ V)           = ((s , V ·-) ▻ M)
step ((s , (V-ƛ t ·-)) ◅ V)       = s ▻ (t [ discharge V ])
step ((s , (-·⋆ A)) ◅ V-Λ t)      = s ▻ (t [ A ]⋆)
step ((s , wrap-) ◅ V)            = s ◅ (V-wrap V)
step ((s , unwrap-) ◅ V-wrap V)   = s ▻ deval V
step (s ▻ (builtin b / refl))     = s ◅ ival b
step ((s , (V-I⇒ b {am = 0} bt ·-)) ◅ vu) = s ▻ BUILTIN' b (app bt vu)
step ((s , (V-I⇒ b {am = suc _} bt ·-)) ◅ vu) = s ◅ V-I b (app bt vu)
step ((s , -·⋆ A) ◅ V-IΠ b  bt)   =  s ◅ V-I b (app⋆ bt refl refl) 
step (□ V)                        = □ V
step (◆ A)                        = ◆ A


 
stepper : ℕ → ∀{T}
  → State T
  → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

