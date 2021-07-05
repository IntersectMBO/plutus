# CK machine

```
module Algorithmic.CK where
```

```
open import Function
open import Data.Bool using (Bool;true;false)
open import Data.List as L using (List;[];_∷_)
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality using (inspect;sym;trans;_≡_;refl;cong)
  renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (tt)
open import Data.Product renaming (_,_ to _,,_)
import Data.Sum as Sum
open import Data.Empty
open import Utils
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNBE
open import Algorithmic.RenamingSubstitution
```

```
open import Algorithmic.ReductionEC renaming (step to app;step⋆ to app⋆)

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
closeFrame (-·⋆ A)         t = _·⋆_ t A
closeFrame wrap-           t = wrap _ _ t
closeFrame unwrap-         t = unwrap t
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
step (s ▻ (L ·⋆ A))               = (s , -·⋆ A) ▻ L
step (s ▻ wrap A B L)             = (s , wrap-) ▻ L
step (s ▻ unwrap L)               = (s , unwrap-) ▻ L
step (s ▻ con cn)                 = s ◅ V-con cn
step (s ▻ error A)                = ◆ A
step (ε ◅ V)                      = □ V
step ((s , (-· M)) ◅ V)           = ((s , V ·-) ▻ M)
step ((s , (V-ƛ t ·-)) ◅ V)       = s ▻ (t [ discharge V ])
step ((s , (-·⋆ A)) ◅ V-Λ t)      = s ▻ (t [ A ]⋆)
step ((s , wrap-) ◅ V)            = s ◅ (V-wrap V)
step ((s , unwrap-) ◅ V-wrap V)   = s ◅ V
step (s ▻ ibuiltin b) = s ◅ ival b
step ((s , (V-I⇒ b {as' = []} p bt ·-)) ◅ vu) =
  s ▻ BUILTIN' b (bubble p) (app p bt vu)
step ((s , (V-I⇒ b {as' = _ ∷ as'} p bt ·-)) ◅ vu) =
  s ◅ V-I b (bubble p) (app p bt vu)
step ((s , -·⋆ A) ◅ V-IΠ b {as' = []} p bt) =
  s ▻ BUILTIN' b (bubble p) (app⋆ p bt)
step ((s , -·⋆ A) ◅ V-IΠ b {as' = x ∷ as'} p bt) =
  s ◅ V-I b (bubble p) (app⋆ p bt)
step (□ V)                        = □ V
step (◆ A)                        = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T}
  → State T
  → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

import Algorithmic.CC as CC
open import Relation.Binary.PropositionalEquality
open import Data.Sum

{-# TERMINATING #-}
helper : ∀{A B} → (B ≡ A) ⊎ (Σ _ λ I → EC B I × Frame I A) → Stack B A

EvalCtx2Stack : ∀ {I J} → EC I J → Stack I J
EvalCtx2Stack E = helper (CC.dissect E)

helper (inj₁ refl) = ε
helper (inj₂ (I ,, E ,, F)) = EvalCtx2Stack E , F

Stack2EvalCtx : ∀ {A B} → Stack A B → EC A B
Stack2EvalCtx ε       = []
Stack2EvalCtx (s , F) = CC.extEC (Stack2EvalCtx s) F

cc2ck : ∀ {I} → CC.State I → State I
cc2ck (x CC.▻ x₁) = EvalCtx2Stack x ▻ x₁
cc2ck (x CC.◅ x₁) = EvalCtx2Stack x ◅ x₁
cc2ck (CC.□ x) = □ x
cc2ck (CC.◆ x) = ◆ x

ck2cc : ∀ {I} → State I → CC.State I
ck2cc (x ▻ x₁) = Stack2EvalCtx x CC.▻ x₁
ck2cc (x ◅ x₁) = Stack2EvalCtx x CC.◅ x₁
ck2cc (□ x) = CC.□ x
ck2cc (◆ x) = CC.◆ x
