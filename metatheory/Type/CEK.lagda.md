# CEK machine

```
module Type.CEK where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_;proj₁;proj₂) renaming (_,_ to _,,_)
open import Function

open import Type
open import Type.Reduction hiding (step)
open import Type.RenamingSubstitution

-- a CEK machine for types

Closure : Kind → Set

data Env : Ctx⋆ → Set where
  [] : Env ∅
  _∷_ : ∀{Φ J} → Env Φ → Closure J → Env (Φ ,⋆ J)

Closure J = Σ Ctx⋆ λ Φ → Σ (Φ ⊢⋆ J) λ A → Value⋆ A × Env Φ

lookup : ∀{Φ K} → Φ ∋⋆ K → Env Φ → Closure K
lookup Z     (ρ ∷ c) = c
lookup (S α) (ρ ∷ c) = lookup α ρ

data Frame : (K : Kind)(H : Kind) → Set where
  -·     : ∀{K J Φ} → Φ ⊢⋆ K → Env Φ → Frame J (K ⇒ J)
  _·-     : ∀{K J} → Closure (K ⇒ J) → Frame J K
  -⇒     : ∀{Φ} → Φ ⊢⋆ * → Env Φ → Frame * *
  _⇒-     : Closure * → Frame * *
  
data Stack (K : Kind) : (H : Kind) → Set where
  ε   : Stack K K
  _,_ : ∀{H1 H2} → Stack K H1 → Frame H1 H2 → Stack K H2

data State (K : Kind) : Set where
  _;_▻_ : {H : Kind} → Stack K H → ∀{Φ} → Env Φ → Φ ⊢⋆ H → State K
  _;_◅_ : {H : Kind} → Stack K H → ∀{Φ} → Env Φ → {A : Φ ⊢⋆ H} → Value⋆ A
    → State K
  □  : Closure K → State K

discharge : ∀{Φ K}{A : Φ ⊢⋆ K} → Value⋆ A → Env Φ → Σ (∅ ⊢⋆ K) Value⋆

env2ren : ∀{Φ} → Env Φ → Sub Φ ∅
env2ren (ρ ∷ (_ ,, A ,, V ,, ρ')) Z     = proj₁ (discharge V ρ')
env2ren (ρ ∷ C)                   (S α) = env2ren ρ α

dischargeBody : ∀{Φ K J} → Φ ,⋆ J ⊢⋆ K → Env Φ → ∅ ,⋆ J ⊢⋆ K
dischargeBody body ρ = subst (exts (env2ren ρ)) body 

dischargeN : ∀{Φ K}{A : Φ ⊢⋆ K} → Neutral⋆ A → Env Φ → Σ (∅ ⊢⋆ K) Neutral⋆

discharge (V-Π A)   ρ = _ ,, V-Π (dischargeBody A ρ)
discharge (A V-⇒ B) ρ =
  _ ,, proj₂ (discharge A ρ) V-⇒ proj₂ (discharge B ρ)
discharge (V-ƛ A)   ρ = _ ,, V-ƛ (dischargeBody A ρ)
discharge (N- N)    ρ = _ ,, N- (proj₂ (dischargeN N ρ))
discharge (V-con c) ρ = _ ,, V-con c

dischargeN N-μ1 ρ = μ1 ,, N-μ1
dischargeN (N-· N V) ρ =
  _ ,, N-· (proj₂ (dischargeN N ρ)) (proj₂ (discharge V ρ))

step : ∀{K} → State K → State K
step (s ; ρ ▻ ` α) = let Φ ,, A ,, V ,, ρ' = lookup α ρ in s ; ρ' ◅ V
step (s ; ρ ▻ Π A) = s ; ρ ◅ V-Π A
step (s ; ρ ▻ (A ⇒ B)) = (s , -⇒ B ρ) ; ρ ▻ A
step (s ; ρ ▻ ƛ A) = s ; ρ ◅ V-ƛ A
step (s ; ρ ▻ (A · B)) = (s , -· B ρ) ; ρ ▻ A
step (s ; ρ ▻ μ1) = s ; ρ ◅ N- N-μ1
step (s ; ρ ▻ con c) = s ; ρ ◅ V-con c
step (ε ; ρ ◅ V) = □ (_ ,, _ ,, V ,, ρ)
step ((s , -· B ρ') ; ρ ◅ V) = (s , ((_ ,, _ ,, V ,, ρ) ·-)) ; ρ' ▻ B
step ((s , ((_ ,, .(ƛ _) ,, V-ƛ M ,, ρ') ·-)) ; ρ ◅ V) =
 s ; ρ' ∷ (_ ,, _ ,, V ,, ρ) ▻ M
step ((s , ((_ ,, _ ,, N- N ,, ρ') ·-)) ; ρ ◅ V) =
  s ; [] ◅ N- (N-· (proj₂ (dischargeN N ρ')) (proj₂ (discharge V ρ)))
step ((s , -⇒ B ρ') ; ρ ◅ V) = (s , ((_ ,, _ ,, V ,, ρ) ⇒-)) ; ρ' ▻ B
step ((s , ((_ ,, _ ,, V ,, ρ') ⇒-)) ; ρ ◅ W) =
  s ; [] ◅ (proj₂ (discharge V ρ') V-⇒ proj₂ (discharge W ρ))
step (□ C)       = □ C
