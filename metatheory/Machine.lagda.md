```
module Machine where
```

```
open import Function

open import Type
open import Type.BetaNormal
open import Algorithmic
open import Algorithmic.Reduction hiding (step)
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf 
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con 
```

```
data Frame {Φ} : (T H : Φ ⊢Nf⋆ *) → Set where

data Stack : ∀{Φ}(A : Φ ⊢Nf⋆ *) → Set where
  ε   : ∀{Φ}{A : Φ ⊢Nf⋆ *} → Stack A
  _,_ : ∀{Φ}{T H : Φ ⊢Nf⋆ *} → Stack T → Frame T H → Stack H
  
data State : Set where
  _▻_ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ} → Stack A → Γ ⊢ A → State
  _◅_ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ} → Stack A → {t : Γ ⊢ A} →  Value t → State
  □_  : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ}{t : Γ ⊢ A} →  Value t → State
  ◆   : ∀{Φ}(A : Φ ⊢Nf⋆ *) → State

{-
step : State → State
step (s ▻ ` x)              = {!!}
step (s ▻ ƛ x L)            = s ◅ V-ƛ {x = x}{N = L}
step (s ▻ (L · M))          = (s , {!!}) ▻ L
step (s ▻ Λ x L)            = {!!}
step (s ▻ (L ·⋆ A))         = (s , {!!}) ▻ L
step (s ▻ wrap1 pat arg L)  = (s , {!!}) ▻ L
step (s ▻ unwrap1 L)        = (s , {!!}) ▻ L
step (s ▻ con {Γ = Γ} cn)   = s ◅ V-con {Γ = Γ} cn
step (s ▻ builtin bn σ tel) = {!!}
step (s ▻ error A)          = ◆ A
step (s ◅ V) = {!s!}
step (□ V)   = □ V
step (◆ A)   = ◆ A
-}
```
