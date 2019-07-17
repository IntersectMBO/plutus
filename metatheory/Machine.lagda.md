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
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNBE
```

```
data Frame : ∀{Φ Φ'}(T : Φ ⊢Nf⋆ *)(H : Φ' ⊢Nf⋆ *) → Set where
  -·_ : ∀{Φ}{Γ}{A B : Φ ⊢Nf⋆ *} → Γ ⊢ A → Frame B (A ⇒ B)
  Λ-  : ∀{Φ}{K}{x}{B : Φ ,⋆ K ⊢Nf⋆ *} → Frame (Π x B) B
  -·⋆_ :  ∀ {Φ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}(A : Φ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π x B)
  wrap- :  ∀{Φ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame (ne (μ1 · pat · arg)) (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{Φ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame (nf (embNf pat · (μ1 · embNf pat) · embNf arg))  (ne (μ1 · pat · arg))
data Stack : ∀{Φ}(A : Φ ⊢Nf⋆ *) → Set where
  ε   : ∀{Φ}{A : Φ ⊢Nf⋆ *} → Stack A
  _,_ : ∀{Φ Φ'}{T : Φ ⊢Nf⋆ *}{H : Φ' ⊢Nf⋆ *} → Stack T → Frame T H → Stack H
  
data State{Φ}(Γ : Ctx Φ) : Set where
  _▻_ : {A : Φ ⊢Nf⋆ *} → Stack A → Γ ⊢ A → State Γ
  _◅_ : {A : Φ ⊢Nf⋆ *} → Stack A → {t : Γ ⊢ A} →  Value t → State Γ
  □_  : {A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A} →  Value t → State Γ
  ◆   : (A : Φ ⊢Nf⋆ *) → State Γ

open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

{-
step : ∀{Φ}{Γ : Ctx Φ} → NoVar Γ → State Γ → Σ Ctx⋆ λ Φ' → Σ (Ctx Φ') State
step {Φ}{Γ} p (s ▻ ` x)              = ⊥-elim (noVar p x)
step {Φ}{Γ} p (s ▻ ƛ x L)            = Φ      ,, Γ      ,, s ◅ V-ƛ {x = x}{N = L}
step {Φ}{Γ} p (s ▻ (L · M))          = Φ      ,, Γ      ,, (s , (-· M)) ▻ L
step {Φ}{Γ} p (s ▻ Λ x L)            = Φ ,⋆ _ ,, Γ ,⋆ _ ,, (s , Λ-) ▻ L
step {Φ}{Γ} p (s ▻ (L ·⋆ A))         = Φ      ,, Γ      ,, (s , (-·⋆ A)) ▻ L
step {Φ}{Γ} p (s ▻ wrap1 pat arg L)  = Φ      ,, Γ      ,, (s , wrap-) ▻ L
step {Φ}{Γ} p (s ▻ unwrap1 L)        = Φ      ,, Γ      ,, (s , unwrap-) ▻ L
step {Φ}{Γ} p (s ▻ con {Γ = Γ} cn)   = Φ      ,, Γ      ,, s ◅ V-con {Γ = Γ} cn
step {Φ}{Γ} p (s ▻ builtin bn σ tel) = Φ      ,, Γ      ,, {!!}
step {Φ}{Γ} p (s ▻ error A)          = Φ      ,, Γ      ,, ◆ A
step {Φ}{Γ} p (s ◅ V) = {!!}
step {Φ}{Γ} p (□ V)   = {!!} ,, {!!} ,, □ V
step {Φ}{Γ} p (◆ A)   = {!!} ,, {!!} ,, ◆ A
-}
```
