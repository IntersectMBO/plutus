# CEK machine that discharges builtin args

```
module Algorithmic.CEKV where

open import Function hiding (_∋_)
open import Data.Product using (proj₁;proj₂)

open import Type
open import Type.BetaNormal
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con

data Env : Ctx ∅ → Set

data Value : (A : ∅ ⊢Nf⋆ *) → Set where
  V-ƛ : ∀ {Γ}{A B : ∅ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
    → Env Γ
    → Value (A ⇒ B)

  V-Λ : ∀ {Γ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
    → Env Γ
    → Value (Π B)

  V-con : {tcn : TyCon}
    → (cn : TermCon {∅} (con tcn))
    → Value (con tcn)

data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Value (A ⇒ B) → Frame B A

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

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _;_◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → Env ∅ → Value H → State T
  □     : Value T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)             = s ; [] ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)             = s ; [] ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))         = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)             = s ; [] ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A))        = (s , -·⋆ A) ; ρ ▻ L 
step (s ; ρ ▻ wrap1 pat arg L) = ◆ (ne ((μ1 · pat) · arg))
step (s ; ρ ▻ unwrap1 {pat = pat}{arg} L) = ◆ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
step (s ; ρ ▻ con c) = s ; [] ◅ V-con c
step (s ; ρ ▻ builtin bn σ ts) = ◆ (substNf σ (proj₂ (proj₂ (SIG bn))))
step (s ; ρ ▻ error A) = ◆ A
step (ε             ; [] ◅ V) = □ V
step ((s , -· M ρ') ; [] ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ; [] ◅ V) = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ; [] ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {pat = pat}{arg = arg})   ; [] ◅ V) =
  ◆ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
step (□ V) = □ V
step (◆ A) = ◆ A
