# CEK machine

```
module Algorithmic.CEK where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open import Type
open import Type.Reduction using (Value⋆)

-- a CK machine for types

Clos⋆ : Ctx⋆ → Kind → Set

data EnvC⋆ : Ctx⋆ → Ctx⋆ → Set where
  [] : ∀{Φ} → EnvC⋆ ∅ Φ
  _,⋆_ : ∀{Φ Ψ J} → EnvC⋆ Φ Ψ → Clos⋆ Ψ J → EnvC⋆ (Φ ,⋆ J) Ψ
  
Clos⋆ Ψ J = Σ Ctx⋆ λ Φ → Φ ⊢⋆ J × EnvC⋆ Φ Ψ

postulate discharge : ∀{Ψ J} → Clos⋆ Ψ J → (Ψ ⊢⋆ J)

data Frame (Φ : Ctx⋆)(K : Kind) : (Φ' : Ctx⋆)(H : Kind) → Set where

data Stack (Φ : Ctx⋆)(K : Kind) : (Φ' : Ctx⋆)(H : Kind) → Set where
  ε   : ∀{Φ}{Γ}{T : Φ ⊢Nf⋆ *} → Stack Γ T Γ T
  _,_ : ∀{Φ Φ' Φ''}{Γ Γ' Γ''}{T : Φ ⊢Nf⋆ *}{H1 : Φ' ⊢Nf⋆ *}{H2 : Φ'' ⊢Nf⋆ *}
    → Stack Γ T Γ' H1
    → Frame Γ' H1 Γ'' H2 → Stack Γ T Γ'' H2
data State (Φ : Ctx⋆)(K : Kind) : (Φ' : Ctx⋆)(H : Kind) → Set where
  _▻_ : ∀{Φ'}{H : Kind} → Stack Φ K Φ H → Φ' ⊢⋆ H → State Φ K Φ' H
  _◅_ : ∀{Φ'}{H : Kind} → Stack Φ K Φ' H → {A : Φ' ⊢⋆ H} → Value⋆ A
    → State Φ K Φ' H 
  □  : {A : Φ ⊢⋆ K} →  Value⋆ A → State Φ K Φ K
  ◆   : ∀ {Φ'}(J : Kind) →  State Φ K Φ' J

step : ∀{Φ Φ' K H} → State Φ K Φ' H → Σ Ctx⋆ λ Φ'' → Σ Kind λ H' → State Φ K Φ'' H 
step = {!!}
