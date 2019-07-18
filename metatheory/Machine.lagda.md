# CK machine

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
open import Algorithmic.RenamingSubstitution
```

```
data Frame : ∀{Φ Φ'} → Ctx Φ → (T : Φ ⊢Nf⋆ *) → Ctx Φ' → (H : Φ' ⊢Nf⋆ *) → Set where
  -·_ : ∀{Φ}{Γ}{A B : Φ ⊢Nf⋆ *} → Γ ⊢ A → Frame Γ B Γ (A ⇒ B)
  _·- : ∀{Φ}{Γ}{A B : Φ ⊢Nf⋆ *}{t : Γ ⊢ A ⇒ B} → Value t → Frame Γ B Γ A
  Λ-  : ∀{Φ}{Γ}{K}{x}{B : Φ ,⋆ K ⊢Nf⋆ *} → Frame Γ (Π x B) (Γ ,⋆ K) B
  -·⋆_ :  ∀ {Φ K Γ x}{B : Φ ,⋆ K ⊢Nf⋆ *}(A : Φ ⊢Nf⋆ K) → Frame Γ (B [ A ]Nf) Γ (Π x B)
  wrap- :  ∀{Φ Γ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame Γ (ne (μ1 · pat · arg)) Γ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{Φ Γ K}{pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : Φ ⊢Nf⋆ K}
    → Frame Γ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))  Γ (ne (μ1 · pat · arg))
data Stack : ∀{Φ}(Γ : Ctx Φ) (A : Φ ⊢Nf⋆ *) → Set where
  ε   : ∀{Φ}{Γ}{A : Φ ⊢Nf⋆ *} → Stack Γ A
  _,_ : ∀{Φ Φ'}{Γ Γ'}{T : Φ ⊢Nf⋆ *}{H : Φ' ⊢Nf⋆ *} → Stack Γ T → Frame Γ T Γ' H → Stack Γ' H
  
data State{Φ}(Γ : Ctx Φ) : Set where
  _▻_ : {A : Φ ⊢Nf⋆ *} → Stack Γ A → Γ ⊢ A → State Γ
  _◅_ : {A : Φ ⊢Nf⋆ *} → Stack Γ A → {t : Γ ⊢ A} →  Value t → State Γ
  □_  : {A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A} →  Value t → State Γ
  ◆   : (A : Φ ⊢Nf⋆ *) → State Γ

open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

-- this function, apart from making a step, also determines the contexts and provides a proof.
-- These things could be done seperately.

-- this could also be presented as a relation and then there would be more function rather like progress

step : ∀{Φ}{Γ : Ctx Φ} → NoVar Γ → State Γ → Σ Ctx⋆ λ Φ' → Σ (Ctx Φ') λ Γ → NoVar Γ × State Γ
step p (s ▻ ` x)                          = ⊥-elim (noVar p x)
step p (s ▻ ƛ x L)                        = _ ,, _ ,, p ,, s ◅ V-ƛ {x = x}{N = L}
step p (s ▻ (L · M))                      = _ ,, _ ,, p ,, (s , -· M) ▻ L
step p (s ▻ Λ x L)                        = _ ,, _ ,, p ,, (s , Λ-) ▻ L
step p (s ▻ (L ·⋆ A))                     = _ ,, _ ,, p ,, (s , -·⋆ A) ▻ L
step p (s ▻ wrap1 pat arg L)              = _ ,, _ ,, p ,, (s , wrap-) ▻ L
step p (s ▻ unwrap1 L)                    = _ ,, _ ,, p ,, (s , unwrap-) ▻ L
step {Γ = Γ} p (s ▻ con cn)               = _ ,, Γ ,, p ,, s ◅ V-con cn
step {Γ = Γ} p (s ▻ builtin bn σ tel)     = _ ,, Γ ,, p ,, ◆ (substNf σ (proj₂ (proj₂ (SIG bn))))
step {Γ = Γ} p (s ▻ error A)              = _ ,, Γ ,, p ,, ◆ A
step p (ε ◅ V)                            = _ ,, _ ,, p ,, □ V
step p ((s , (-· M)) ◅ V)                 = _ ,, _ ,, p ,, ((s , V ·-) ▻ M)
step p (_◅_ (s , (V-ƛ {N = t} ·-)) {u} V) = _ ,, _ ,, p ,, s ▻ (t [ u ])
step p ((s , Λ-) ◅ V)                     = _ ,, _ ,, p ,, s ◅ V-Λ V
step p ((s , (-·⋆ A)) ◅ V-Λ {N = t} V)    = _ ,, _ ,, p ,, s ▻ (t [ A ]⋆)
step p ((s , wrap-) ◅ V)                  = _ ,, _ ,, p ,, s ◅ (V-wrap V)
step p ((s , unwrap-) ◅ V-wrap V)         = _ ,, _ ,, p ,, s ◅ V
step p (□ V)                              = _ ,, _ ,, p ,, □ V
step {Γ = Γ} p (◆ A)                      = _ ,, Γ ,, p ,, ◆ A
```

```
open import Data.Nat
open import Data.Maybe

stepper : ℕ → ∀{Φ}{Γ : Ctx Φ} → NoVar Γ → State Γ → Σ Ctx⋆ λ Φ' → Σ (Ctx Φ') λ Γ → NoVar Γ × Maybe (State Γ)
stepper zero {Γ = Γ} p st = _ ,, Γ ,, p ,, nothing 
stepper (suc n) p st with step p st
stepper (suc n) p st | Φ ,, Γ ,, q ,, (s ▻ M) = stepper n q (s ▻ M)
stepper (suc n) p st | Φ ,, Γ ,, q ,, (s ◅ V) = stepper n q (s ◅ V)
stepper (suc n) p st | Φ ,, Γ ,, q ,, (□ V)   = Φ ,, Γ ,, q ,, just (□ V)
stepper (suc n) p st | Φ ,, Γ ,, q ,, ◆ A     = Φ ,, Γ ,, q ,, just (◆ A)
```

This is the property I would like to have, but it cannot be proved directly like this:

```
open import Relation.Binary.PropositionalEquality

preservation : ∀ n {Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(p : NoVar Γ)(t : Γ ⊢ A)
  → Σ (Φ ⊢Nf⋆ *) λ A' → Σ (Γ ⊢ A') λ t' → Σ (Value t') λ v → stepper n p (ε ▻ t) ≡ (Φ ,, Γ ,, p ,, just (□ v)) → A ≡ A'

```
