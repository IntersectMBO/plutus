# CEK machine

```
module Algorithmic.CEK where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open import Type
open import Type.BetaNormal
open import Type.BetaNBE hiding (Env)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.Reduction hiding (step)

Clos : ∀{Φ} → Φ ⊢Nf⋆ * → Set
--Clos⋆ : Kind → Set

data Env : ∀{Φ} → Ctx Φ → Set where
  []   : Env ∅
--  _,⋆_ : ∀{Φ J}{Γ : Ctx Φ} → Env Γ → Clos⋆ J → Env (Γ ,⋆ J)
  _,_ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ} → Env Γ → Clos A → Env (Γ , A)

Clos  A = Σ Ctx⋆ λ Φ → Σ (Φ ⊢Nf⋆ *) λ A → Σ (Ctx Φ) λ Γ → Γ ⊢ A × Env Γ

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Clos (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (ne (μ1 · pat · arg))
            (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
            (ne (μ1 · pat · arg))

data Stack (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  ε   : Stack T T
  _,_ : ∀{H1 H2} → Stack T H1 → Frame H1 H2 → Stack T H2

postulate subE : ∀{Φ}{Γ : Ctx Φ} → Φ ⊢Nf⋆ * → Env Γ → ∅ ⊢Nf⋆ *

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Φ}{Γ : Ctx Φ}{H}(ρ : Env Γ) → Stack T (subE H ρ) → Γ ⊢ H → State T
  _;_◅_ : ∀{Φ}{Γ : Ctx Φ}{H}(ρ : Env Γ) → Stack T (subE H ρ) → {M : Γ ⊢ H} → Value M → State T
  □  : Clos T → State T
  ◆  : ∀{Φ} → Φ ⊢Nf⋆ * → State T
{-
step : ∀{Φ Φ' K H} → State Φ K Φ' H → Σ Ctx⋆ λ Φ'' → Σ Kind λ H' → State Φ K Φ'' H 
step = {!!}
-}
