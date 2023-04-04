```
module Algorithmic.ReductionEC.Progress where
```
## Imports

```
open import Data.Nat using (zero;suc)
open import Data.List as List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_;refl)  

open import Utils using (*;bubble)
open import Type using (Ctx⋆;∅)
open import Algorithmic using (Ctx;_⊢_)
open Ctx
open _⊢_

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic.ReductionEC using (Value;BApp;_—→⋆_;_—→_;Error;EC;V-I;ival;E-error)
open Value
open BApp
open _—→⋆_
open _—→_
open EC
```

# Progress proof

```
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

  error :
      Error M
      -------
    → Progress M
```


```
progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress (ƛ M)        = done (V-ƛ M)
progress (M · M')     with progress M
... | error E-error = step (ruleErr ([] l· M') refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E l· M') refl)
... | done VM with progress M'
... | step (ruleEC E p refl refl) = step (ruleEC (VM ·r E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (VM ·r E) refl)
... | error E-error = step (ruleErr (VM ·r []) refl)
progress (.(ƛ M) · M') | done (V-ƛ M) | done VM' =
  step (ruleEC [] (β-ƛ VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = 0} q) | done VM' =
  step (ruleEC [] (β-builtin b M q M' VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = suc _} q) | done VM' =
  done (V-I b (step q VM'))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A / refl) with progress M
... | error E-error = step (ruleErr ([] ·⋆ A / refl) refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E ·⋆ A / refl) refl)
... | done (V-Λ M') = step (ruleEC [] (β-Λ refl) refl refl)
progress (M ·⋆ A / refl) | done (V-IΠ b {tm = 0} q) = done (V-I b (step⋆ q refl refl))
progress (M ·⋆ A / refl) | done (V-IΠ b {tm = suc _} q) =
  done (V-I b (step⋆ q refl refl))
progress (wrap A B M) with progress M
... | done V            = done (V-wrap V)
... | step (ruleEC E p refl refl) = step (ruleEC (wrap E) p refl refl)
... | step (ruleErr E refl)  = step (ruleErr (wrap E) refl)
... | error E-error     = step (ruleErr (wrap []) refl)
progress (unwrap M refl) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (unwrap E / refl) refl)
... | done (V-wrap V) = step (ruleEC [] (β-wrap V refl) refl refl)
... | error E-error = step (ruleErr (unwrap [] / refl) refl)
progress (con c)      = done (V-con c)
progress (builtin b / refl ) = done (ival b)
progress (error A)    = error E-error

{- These definitions seems unused
_↓ : ∀{A} → ∅ ⊢ A → Set
M ↓ = ∃ λ M' → M —→⋆ M'

-- progress in disguise
lemma51 : ∀{A}(M : ∅ ⊢ A)
        → Value M
        ⊎ ∃ λ B
        → ∃ λ (E : EC A B)
        → ∃ λ (L : ∅ ⊢ B)
        → (L ↓ ⊎ Error L)
        × M ≡ E [ L ]ᴱ
lemma51 (ƛ M) = inj₁ (V-ƛ M)
lemma51 (M · M') with lemma51 M
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E l· M' ,, L ,, p ,, cong (_· M') q)
... | inj₁ VM with lemma51 M'
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, VM ·r E ,, L ,, p ,, cong (M ·_) q)
lemma51 (.(ƛ M) · M') | inj₁ (V-ƛ M)      | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-ƛ VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = []} p x) | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-builtin b M p x M' VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = a ∷ as'} p x) | inj₁ VM' =
  inj₁ (V-I b (bubble p) (step p x VM'))
lemma51 (Λ M) = inj₁ (V-Λ M)
lemma51 (M ·⋆ A / refl) with lemma51 M
... | inj₁ (V-Λ M') =
  inj₂ (_ ,, [] ,, M ·⋆ A / refl ,, inj₁ (M' [ A ]⋆ ,, (β-Λ refl)) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E ·⋆ A / refl ,, L ,, p ,, cong (_·⋆ A / refl) q)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = []} p x) =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-builtin⋆ b M p x A refl) ,, refl)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = a ∷ as} p x) =
  inj₁ (V-I b (bubble p) (step⋆ p x refl))
lemma51 (wrap A B M) with lemma51 M
... | inj₁ V = inj₁ (V-wrap V)
... | inj₂ (C ,, E ,, L ,, p ,, p') =
  inj₂ (C ,, wrap E ,, L ,, p ,, cong (wrap A B) p')
lemma51 (unwrap M refl) with lemma51 M
... | inj₁ (V-wrap V) =
  inj₂ (_ ,, [] ,, unwrap M refl ,, inj₁ (deval V ,, β-wrap V refl) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, p') =
  inj₂ (B ,, unwrap E / refl ,, L ,, p ,, cong (λ x → unwrap x refl) p')
lemma51 (con c) = inj₁ (V-con c)
lemma51 (builtin b / refl) = inj₁ (ival b)
lemma51 (error _) = inj₂ (_ ,, ([] ,, (error _ ,, (inj₂ E-error) ,, refl)))

progress' : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, refl) = step (ruleEC E p refl refl)
... | inj₂ (B ,, E ,, L ,, inj₂ E-error ,, refl) = step (ruleErr E refl)

-}
 