# CEK machine

```
module Algorithmic.CEK where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_)

open import Type
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.Reduction -- for values

{-
Clos⋆ : Ctx⋆ → Kind → Set
EnvC⋆ : Ctx⋆ → Ctx⋆ → Set

EnvC⋆ Φ Ψ = ∀{J} → Φ ∋⋆ J → Clos⋆ Ψ J 
Clos⋆ Ψ J = Σ Ctx⋆ λ Φ → EnvC⋆ Φ Ψ × Φ ⊢Nf⋆ J
==
Clos⋆ Ψ J = Σ Ctx⋆ λ Φ → (∀{J} → Φ ∋⋆ J → Clos⋆ Ψ J) × Φ ⊢Nf⋆ J
-- ^ termination checker understandably not keen
-}

Clos⋆ : Ctx⋆ → Kind → Set

data EnvC⋆ : Ctx⋆ → Ctx⋆ → Set where
  [] : ∀{Φ} → EnvC⋆ ∅ Φ
  _∷_ : ∀{Φ Ψ J} → EnvC⋆ Φ Ψ → Clos⋆ Ψ J → EnvC⋆ (Φ ,⋆ J) Ψ
  
Clos⋆ Ψ J = Σ Ctx⋆ λ Φ → EnvC⋆ Φ Ψ × Φ ⊢Nf⋆ J


Clos : ∀{Φ} → Ctx Φ → Set
data EnvC : ∀{Φ Ψ} → EnvC⋆ Φ Ψ → Ctx Φ → Ctx Ψ → Set where
Clos {Φ} Γ =
  Σ Ctx⋆ λ Ψ → Σ (Ctx Ψ) λ Δ
  → Σ (EnvC⋆ Ψ Φ) λ ρ⋆ → EnvC ρ⋆ Δ Γ × Σ (Ψ ⊢Nf⋆ *) λ A → Σ (Δ ⊢ A) Value


data Frame : ∀{Φ Φ'} → Ctx Φ → (T : Φ ⊢Nf⋆ *) → Ctx Φ' → (H : Φ' ⊢Nf⋆ *) → Set
  where
  -·_     : ∀{Φ}{Γ}{A B : Φ ⊢Nf⋆ *} → Γ ⊢ A → Frame Γ B Γ (A ⇒ B)
  _·-     : ∀{Φ}{Γ}{A B : Φ ⊢Nf⋆ *}{t : Γ ⊢ A ⇒ B} → Value t → Frame Γ B Γ A
  -·⋆    : ∀{Φ K Γ}{B : Φ ,⋆ K ⊢Nf⋆ *}(A : Φ ⊢Nf⋆ K)
    → Frame Γ (B [ A ]Nf) Γ (Π B)
  wrap-   : ∀{Φ Γ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame Γ (ne (μ1 · pat · arg))
            Γ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{Φ Γ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame Γ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
            Γ (ne (μ1 · pat · arg))
