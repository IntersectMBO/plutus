# CK machine

```
module Algorithmic.CK where
```

```
open import Function
open import Data.Bool using (Bool;true;false)

open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
open import Algorithmic.Reduction hiding (step)
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNBE
open import Algorithmic.RenamingSubstitution
```

```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (ne (μ1 · pat · arg))
            (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
            (ne (μ1 · pat · arg))

data Stack : (T : ∅ ⊢Nf⋆ *)(H : ∅ ⊢Nf⋆ *) → Set where
  ε   : {T : ∅ ⊢Nf⋆ *} → Stack T T
  _,_ : {T : ∅ ⊢Nf⋆ *}{H1 : ∅ ⊢Nf⋆ *}{H2 : ∅ ⊢Nf⋆ *}
    → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  _▻_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → ∅ ⊢ H → State T H
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → {t : ∅ ⊢ H} → Value t → State T H
  □  : {t : ∅ ⊢ T} →  Value t → State T T
  ◆   : (A : ∅ ⊢Nf⋆ *)  →  State T A

-- Plugging a term of suitable type into a frame yields a term again

closeFrame : ∀{T H} → Frame T H → ∅ ⊢ H → ∅ ⊢ T
closeFrame (-· u)          t = t · u
closeFrame (_·- {t = t} v) u = t · u
closeFrame (-·⋆ A)         t = _·⋆_ t A
closeFrame wrap-           t = wrap1 _ _ t
closeFrame unwrap-         t = unwrap1 t

-- Plugging a term into a stack yields a term again

closeStack : ∀{T H} → Stack T H → ∅ ⊢ H → ∅ ⊢ T
closeStack ε       t = t
closeStack (s , f) t = closeStack s (closeFrame f t)

-- a state can be closed to yield a term again

closeState : ∀{T H} → State T H → ∅ ⊢ T
closeState (s ▻ t)           = closeStack s t
closeState (_◅_ s {t = t} v) = closeStack s t
closeState (□ {t = t} v)     = t
closeState (◆ A)             = error _


open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

-- this function, apart from making a step, also determines the
-- contexts and provides a proof.  These things could be done
-- seperately.

-- this could also be presented as a relation and then there would be
-- more function rather like progress

step : ∀{A H} → State A H → Σ (∅ ⊢Nf⋆ *) (State A)
step (s ▻ ƛ L)                          = _ ,, s ◅ V-ƛ {N = L}
step (s ▻ (L · M))                      = _ ,, (s , -· M) ▻ L
step (s ▻ Λ L)                          = _ ,, s ◅ V-Λ {N = L}
step (s ▻ (_·⋆_ L A))                   = _ ,, (s , -·⋆ A) ▻ L
step (s ▻ wrap1 pat arg L)              = _ ,, (s , wrap-) ▻ L
step (s ▻ unwrap1 L)                    = _ ,, (s , unwrap-) ▻ L
step (s ▻ con cn)                       = _ ,, s ◅ V-con cn
step (s ▻ builtin bn σ tel)             =
  _ ,, ◆ (substNf σ (proj₂ (proj₂ (SIG bn))))
step (s ▻ error A)                      = _ ,, ◆ A
step (ε ◅ V)                            = _ ,, □ V
step ((s , (-· M)) ◅ V)                 = _ ,, ((s , V ·-) ▻ M)
step (_◅_ (s , (V-ƛ {N = t} ·-)) {u} V) = _ ,, s ▻ (t [ u ])
step ((s , (-·⋆ A)) ◅ V-Λ {N = t})      = _ ,, s ▻ (t [ A ]⋆)
step ((s , wrap-) ◅ V)                  = _ ,, s ◅ (V-wrap V)
step ((s , unwrap-) ◅ V-wrap V)         = _ ,, s ◅ V
step (□ V)                              = _ ,, □ V
step (◆ A)                              = _ ,, ◆ A
```

```
open import Data.Nat
open import Data.Maybe

stepper : ℕ → ∀{T H}
  → State T H
  → Σ (∅ ⊢Nf⋆ *) λ H → Maybe (State T H)
stepper zero {H = H} st = H ,, nothing 
stepper (suc n) st with step st
stepper (suc n) st | _ ,, (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | _ ,, (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | _ ,, (□ V)   = _ ,, just (□ V)
stepper (suc n) st | _ ,, ◆ A     = _ ,, just (◆ A)
```

This is the property I would like to have, but it cannot be proved directly like this:

```
open import Relation.Binary.PropositionalEquality

{-
preservation : ∀ n {Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(p : NoVar Γ)(t : Γ ⊢ A)
  → Σ (Φ ⊢Nf⋆ *) λ A' → Σ (Γ ⊢ A') λ t' → Σ (Value t') λ v → stepper n p (ε ▻ t) ≡ (Φ ,, Γ ,, p ,, just (□ v)) → A ≡ A'
-}
```
