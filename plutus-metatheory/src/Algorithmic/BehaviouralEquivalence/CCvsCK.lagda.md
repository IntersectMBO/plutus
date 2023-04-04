# CK machine

```
module Algorithmic.BehaviouralEquivalence.CCvsCK where
```

## Imports

```
open import Data.Bool using (Bool;true;false)
open import Data.List as L using (List;[];_∷_)
open import Relation.Binary.PropositionalEquality using (inspect;_≡_;refl;cong)
                                                  renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (tt)
open import Data.Integer using (+_)
open import Data.Product using (Σ;_×_;∃) renaming (_,_ to _,,_)
import Data.Sum as Sum
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Sum using (_⊎_;inj₁;inj₂)

open import Utils using (Kind;*;_⇒_;Either;inj₁;bubble;RuntimeError;Monad)
open RuntimeError
open Monad {{...}}

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic using (Ctx;_⊢_)
open Ctx
open _⊢_

open import Builtin using (Builtin)
open Builtin.Builtin

open import Builtin.Constant.Type using (TyCon)
open TyCon

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon

open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.ReductionEC using (Frame;Value;deval;ival;BUILTIN';V-I;EC) 
                                    renaming (step to app;step⋆ to app⋆)
open Frame
open Value
open EC

import Algorithmic.CC as CC
import Algorithmic.BehaviouralEquivalence.ReductionvsCC as CC

open import Algorithmic.CK
```

# BehaviouralEquivalence

```
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

thm64 : ∀{A}(E : CC.State A)(E' : CC.State A)
  → E CC.-→s E' → cc2ck E -→s cc2ck E'
thm64 E .E CC.base = base
thm64 (E CC.▻ ƛ M) E' (CC.step* refl p) = step* refl (thm64 _ E' p)
thm64 (E CC.▻ (M · N)) E' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E (-· N))) (thm64 _ E' p)
thm64 (E CC.▻ Λ M) E' (CC.step* refl p) = step* refl (thm64 _ E' p)
thm64 (E CC.▻ (M ·⋆ A / refl)) E' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E (-·⋆ A))) (thm64 _ E' p)
thm64 (E CC.▻ wrap A B M) E' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E wrap-)) (thm64 _ E' p)
thm64 (E CC.▻ unwrap M refl) E' (CC.step* refl p) =
  step* (cong (λ E → E ▻ M) (lemmaH E unwrap-)) (thm64 _ E' p)
thm64 (E CC.▻ con M) E' (CC.step* refl p) =
  step* refl (thm64 _ E' p)
thm64 (E CC.▻ (builtin b / refl)) E' (CC.step* refl p) =
  step* refl (thm64 _ E' p)
thm64 (E CC.▻ error _) E' (CC.step* refl p) = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V) E' (CC.step* refl p) with CC.dissect E | inspect CC.dissect E
... | inj₁ refl | [[ eq ]] rewrite CC.dissect-inj₁ E refl eq =
  step* refl (thm64 _ E' p)
... | inj₂ (_ ,, E'' ,, (-· N)) | [[ eq ]] =
  step* (cong (λ p → p ▻ N) (lemmaH E'' (V ·-))) (thm64 _ E' p)
... | inj₂ (_ ,, E'' ,, (V-ƛ M ·-)) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V) E' (CC.step* refl p) | inj₂ (_ ,, E'' ,, (V-I⇒ b {am = 0} x ·-)) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V) E' (CC.step* refl p) | inj₂ (_ ,, E'' ,, (V-I⇒ b {am = suc _} x ·-)) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V-Λ M) E' (CC.step* refl p) | inj₂ (_ ,, E'' ,, -·⋆ A) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V-IΠ b x) E' (CC.step* refl p) | inj₂ (_ ,, E'' ,, -·⋆ A) | [[ eq ]] = step* refl (thm64 _ E' p)
... | inj₂ (_ ,, E'' ,, wrap-) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (E CC.◅ V-wrap V) E' (CC.step* refl p) | inj₂ (_ ,, E'' ,, unwrap-) | [[ eq ]] = step* refl (thm64 _ E' p)
thm64 (CC.□ V) E' (CC.step* refl p) = step* refl (thm64 _ E' p)
thm64 (CC.◆ A) E' (CC.step* refl p) = step* refl (thm64 _ E' p)

thm64b : ∀{A}(s : State A)(s' : State A)
  → s -→s s' → ck2cc s CC.-→s ck2cc s'
thm64b s .s base = CC.base
thm64b (s ▻ ƛ M) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ (M · M₁)) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ Λ M) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ (M ·⋆ A / refl)) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ wrap A B M) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ unwrap M refl) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ con c) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ (builtin b / refl)) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (s ▻ error _) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (ε ◅ V) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b ((s , (-· M)) ◅ V) s' (step* refl p) = CC.step*
  (cong (CC.stepV V) (CC.dissect-lemma (Stack2EvalCtx s) (-· M)))
  (thm64b _ s' p)
thm64b ((s , (V-ƛ M ·-)) ◅ V) s' (step* refl p) = CC.step*
  ((cong (CC.stepV V) (CC.dissect-lemma (Stack2EvalCtx s) (V-ƛ M ·-))))
  (thm64b _ s' p)
thm64b ((s , (VI@(V-I⇒ b {am = 0} x) ·-)) ◅ V) s' (step* refl p) =
  CC.step*
    (cong (CC.stepV V) (CC.dissect-lemma (Stack2EvalCtx s) (VI ·-)))
    (thm64b _ s' p)
thm64b ((s , (VI@(V-I⇒ b {am = suc _} x) ·-)) ◅ V) s' (step* refl p) =
  CC.step*
    (cong (CC.stepV V) (CC.dissect-lemma (Stack2EvalCtx s) (VI ·-)))
    (thm64b _ s' p)
thm64b ((s , -·⋆ A) ◅ V-Λ M) s' (step* refl p) = CC.step*
  (cong (CC.stepV (V-Λ M)) (CC.dissect-lemma (Stack2EvalCtx s) (-·⋆ A)))
  (thm64b _ s' p)
thm64b ((s , -·⋆ A) ◅ VI@(V-IΠ b x)) s' (step* refl p) =
  CC.step*
    (cong (CC.stepV VI) (CC.dissect-lemma (Stack2EvalCtx s) (-·⋆ A)))
    (thm64b _ s' p)
thm64b ((s , wrap-) ◅ V) s' (step* refl p) = CC.step*
  (cong (CC.stepV V) (CC.dissect-lemma (Stack2EvalCtx s) wrap-))
  (thm64b _ s' p)
thm64b ((s , unwrap-) ◅ V-wrap V) s' (step* refl p) = CC.step*
  ((cong (CC.stepV (V-wrap V)) (CC.dissect-lemma (Stack2EvalCtx s) unwrap-)))
  (thm64b _ s' p)
thm64b (□ x₁) s' (step* refl p) = CC.step* refl (thm64b _ s' p)
thm64b (◆ A) s' (step* refl p) = CC.step* refl (thm64b _ s' p)

test : State (con unit)
test = ε ▻ (ƛ (con unit) · (builtin iData / refl · con (integer (+ 0))))

postulate
  lemV : ∀{A B}(M : ∅ ⊢ B)(V : Value M)(E : Stack A B) → (E ▻ M) -→s (E ◅ V)

lem□ : ∀{A}{M M' : ∅ ⊢ A}(V : Value M)(V' : Value M')
  → □ V -→s □ V' → ∃ λ p → substEq Value p V ≡ V'
lem□ W .W base = refl ,, refl
lem□ W V (step* refl p) = lem□ {M = deval W}{M' = deval V} W V p

lem◆ : ∀ {A A' T} → ◆ {T = T} A -→s ◆ A' → A ≡ A'
lem◆ base = refl
lem◆ (step* refl p) = lem◆ p

lem◆' : ∀ {A A'}{M : ∅ ⊢ A}(V : Value M) → ◆ A' -→s □ V → ⊥
lem◆' V (step* refl p) = lem◆' V p


