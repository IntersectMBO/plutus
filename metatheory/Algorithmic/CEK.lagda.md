# CEK machine

```
module Algorithmic.CEK where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_;proj₁;proj₂) renaming (_,_ to _,,_)
open import Function using (_∘_)

open import Type
open import Type.BetaNormal
open import Type.BetaNBE hiding (Env)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.Reduction hiding (step)
open import Algorithmic.RenamingSubstitution
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con

Clos : ∅ ⊢Nf⋆ * → Set

data Env : Ctx ∅ → Set where
  []   : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Clos A → Env (Γ , A)

Clos A = Σ (Ctx ∅) λ Γ → Σ (Γ ⊢ A) λ M → Value M × Env Γ

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Clos A
lookup Z     (ρ ∷ c) = c
lookup (S x) (ρ ∷ c) = lookup x ρ

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
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

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _;_◅_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → {M : Γ ⊢ H} → Value M → State T
  □     : Clos T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)      = let Γ ,, M ,, V ,, ρ' = lookup x ρ in s ; ρ' ◅ V
step (s ; ρ ▻ ƛ M)      = s ; ρ ◅ V-ƛ {N = M}
step (s ; ρ ▻ (L · M))  = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ M)      = s ; ρ ◅ V-Λ {N = M}
step (s ; ρ ▻ (M ·⋆ A)) = (s , -·⋆ A) ; ρ ▻ M
step (s ; ρ ▻ wrap1 pat arg M) = (s , wrap-) ; ρ ▻ M
step (s ; ρ ▻ unwrap1 M) = (s , unwrap-) ; ρ ▻ M
step (s ; ρ ▻ con c) = s ; ρ ◅ V-con c
step (s ; ρ ▻ builtin bn σ ts) = ◆ (substNf σ (proj₂ (proj₂ (SIG bn))))
step (s ; ρ ▻ error A) = ◆ A
step (ε ; ρ ◅ V) = □ (_ ,, _ ,, V ,, ρ)
step ((s , -· M ρ') ; ρ ◅ V) = (s , ((_ ,, _ ,, V ,, ρ) ·-)) ; ρ' ▻ M
step ((s , ((_ ,, ƛ M ,, V-ƛ ,, ρ') ·-)) ; ρ ◅ V) =
  s ; ρ' ∷ (_ ,, _ ,, V ,, ρ) ▻ M
step ((s , -·⋆ A) ; ρ ◅ V-Λ {N = M}) = s ; ρ ▻ (M [ A ]⋆) 
step ((s , wrap-) ; ρ ◅ V) = s ; ρ ◅ V-wrap V
step ((s , unwrap-) ; ρ ◅ V-wrap V) = s ; ρ ◅ V

step (□ C)       = □ C
step (◆ A)       = ◆ A

