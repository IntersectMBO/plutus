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
step ((s , unwrap-) ◅ V-wrap V)   = s ▻ deval V
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

lemmaH : ∀{I J K}(E : EC K J)(F : Frame J I)
  → (helper (CC.dissect E) , F) ≡ helper (CC.dissect (CC.extEC E F))
lemmaH E F rewrite CC.dissect-lemma E F = refl

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

data _-→s_ {A : ∅ ⊢Nf⋆ *} : State A → State A → Set where
  base  : {s : State A} → s -→s s
  step* : {s s' s'' : State A}
        → step s ≡ s'
        → s' -→s s''
        → s -→s s''

step** : ∀{A}{s : State A}{s' : State A}{s'' : State A}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

thm64 : ∀{A}(E : CC.State A)(s' : CC.State A)
  → E CC.-→s s' → cc2ck E -→s cc2ck s'
thm64 E .E CC.base = base
thm64 (E CC.▻ ƛ M) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (E CC.▻ (M · N)) s' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E (-· N))) (thm64 _ s' p)
thm64 (E CC.▻ Λ M) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (E CC.▻ (M ·⋆ A)) s' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E (-·⋆ A))) (thm64 _ s' p)
thm64 (E CC.▻ wrap A B M) s' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E wrap-)) (thm64 _ s' p)
thm64 (E CC.▻ unwrap M) s' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E unwrap-)) (thm64 _ s' p)
thm64 (E CC.▻ con M) s' (CC.step* refl p) =
  step* refl (thm64 _ s' p)
thm64 (E CC.▻ ibuiltin b) s' (CC.step* refl p) =
  step* refl (thm64 _ s' p)
thm64 (E CC.▻ error _) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V) s' (CC.step* refl p) with CC.dissect E | inspect CC.dissect E
... | inj₁ refl | [[ eq ]] rewrite CC.dissect-inj₁ E refl eq =
  step* refl (thm64 _ s' p)
... | inj₂ (_ ,, E' ,, (-· N)) | [[ eq ]] =
  step* (cong (λ p → p ▻ N) (lemmaH E' (V ·-))) (thm64 _ s' p)
... | inj₂ (_ ,, E' ,, (V-ƛ M ·-)) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, (V-I⇒ b {as' = []} p₁ x ·-)) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, (V-I⇒ b {as' = x₁ ∷ as'} p₁ x ·-)) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V-Λ M) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, -·⋆ A) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V-IΠ b {as' = []} p₁ x) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, -·⋆ A) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V-IΠ b {as' = x₁ ∷ as'} p₁ x) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, -·⋆ A) | [[ eq ]] = step* refl (thm64 _ s' p)
... | inj₂ (_ ,, E' ,, wrap-) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (E CC.◅ V-wrap V) s' (CC.step* refl p) | inj₂ (_ ,, E' ,, unwrap-) | [[ eq ]] = step* refl (thm64 _ s' p)
thm64 (CC.□ V) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (CC.◆ A) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
