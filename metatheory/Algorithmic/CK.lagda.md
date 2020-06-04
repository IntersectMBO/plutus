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

data Stack : ∀{Φ Φ'}(Γ : Ctx Φ)(T : Φ ⊢Nf⋆ *)(Γ' : Ctx Φ')(H : Φ' ⊢Nf⋆ *) → Set
  where
  ε   : ∀{Φ}{Γ}{T : Φ ⊢Nf⋆ *} → Stack Γ T Γ T
  _,_ : ∀{Φ Φ' Φ''}{Γ Γ' Γ''}{T : Φ ⊢Nf⋆ *}{H1 : Φ' ⊢Nf⋆ *}{H2 : Φ'' ⊢Nf⋆ *}
    → Stack Γ T Γ' H1
    → Frame Γ' H1 Γ'' H2 → Stack Γ T Γ'' H2

data State {Φ}(Γ : Ctx Φ)(T : Φ ⊢Nf⋆ *) : ∀{Φ'}(Γ' : Ctx Φ')(H : Φ' ⊢Nf⋆ *)
  → Set where
  _▻_ : ∀{Φ' Γ'}{H : Φ' ⊢Nf⋆ *} → Stack Γ T Γ' H → Γ' ⊢ H → State Γ T Γ' H
  _◅_ : ∀{Φ' Γ'}{H : Φ' ⊢Nf⋆ *} → Stack Γ T Γ' H → {t : Γ' ⊢ H} → Value t
    → State Γ T Γ' H 
  □  : {t : Γ ⊢ T} →  Value t → State Γ T Γ T
  ◆   : ∀ {Φ'} Γ' (A : Φ' ⊢Nf⋆ *)  →  State Γ T Γ' A


-- Plugging a term of suitable type into a frame yields a term again

closeFrame : ∀{Φ}{Γ : Ctx Φ}{T : Φ ⊢Nf⋆ *} → ∀{Φ'}{Γ' : Ctx Φ'}{H : Φ' ⊢Nf⋆ *}
  → Frame Γ T Γ' H → Γ' ⊢ H →  Γ ⊢ T
closeFrame (-· u)          t = t · u
closeFrame (_·- {t = t} v) u = t · u
closeFrame (-·⋆ A)         t = _·⋆_ t A
closeFrame wrap-           t = wrap1 _ _ t
closeFrame unwrap-         t = unwrap1 t


-- Plugging a term into a stack yields a term again

closeStack : ∀{Φ}{Γ : Ctx Φ}{T : Φ ⊢Nf⋆ *} → ∀{Φ'}{Γ' : Ctx Φ'}{H : Φ' ⊢Nf⋆ *}
  → Stack Γ T Γ' H → Γ' ⊢ H → Γ ⊢ T
closeStack ε       t = t
closeStack (s , f) t = closeStack s (closeFrame f t)

-- a state can be closed to yield a term again

closeState : ∀{Φ}{Γ : Ctx Φ}{T : Φ ⊢Nf⋆ *} → ∀{Φ'}{Γ' : Ctx Φ'}{H : Φ' ⊢Nf⋆ *}
  → State Γ T Γ' H → Γ ⊢ T
closeState (s ▻ t)           = closeStack s t
closeState (_◅_ s {t = t} v) = closeStack s t
closeState (□ {t = t} v)     = t
closeState (◆ Γ' A)          = error _

open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

-- this function, apart from making a step, also determines the
-- contexts and provides a proof.  These things could be done
-- seperately.

-- this could also be presented as a relation and then there would be
-- more function rather like progress

step : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{A : Φ ⊢Nf⋆ *}{H : Φ' ⊢Nf⋆ *}
  → NoVar Γ'
  → State Γ A Γ' H
  → Σ Ctx⋆ λ Φ''
  → Σ (Ctx Φ'') λ Γ''
  → NoVar Γ'' × Σ (Φ'' ⊢Nf⋆ *) (State Γ A Γ'')
step p (s ▻ ` x)                          = ⊥-elim (noVar p x)
step p (s ▻ ƛ L)                          = _ ,, _ ,, p ,, _ ,, s ◅ V-ƛ {N = L}
step p (s ▻ (L · M))                      = _ ,, _ ,, p ,, _ ,, (s , -· M) ▻ L
step p (s ▻ Λ L)                          = _ ,, _ ,, p ,, _ ,, s ◅ V-Λ {N = L}
step p (s ▻ (_·⋆_ L A))                   = _ ,, _ ,, p ,, _ ,, (s , -·⋆ A) ▻ L
step p (s ▻ wrap1 pat arg L)              = _ ,, _ ,, p ,, _ ,, (s , wrap-) ▻ L
step p (s ▻ unwrap1 L)                    = _ ,, _ ,, p ,, _ ,, (s , unwrap-) ▻ L
step {Γ' = Γ'} p (s ▻ con cn)             = _ ,, Γ' ,, p ,, _ ,, s ◅ V-con cn
step {Γ' = Γ'} p (s ▻ builtin bn σ tel)   =
  _ ,, Γ' ,, p ,, _ ,, ◆ Γ' (substNf σ (proj₂ (proj₂ (SIG bn))))
step {Γ' = Γ'} p (s ▻ error A)            =  _ ,, Γ' ,, p ,, _ ,, ◆ Γ' A
step p (ε ◅ V)                            = _ ,, _ ,, p ,, _ ,, □ V
step p ((s , (-· M)) ◅ V)                 = _ ,, _ ,, p ,, _ ,, ((s , V ·-) ▻ M)
step p (_◅_ (s , (V-ƛ {N = t} ·-)) {u} V) = _ ,, _ ,, p ,, _ ,, s ▻ (t [ u ])
step p ((s , (-·⋆ A)) ◅ V-Λ {N = t})      = _ ,, _ ,, p ,, _ ,, s ▻ (t [ A ]⋆)
step p ((s , wrap-) ◅ V)                  = _ ,, _ ,, p ,, _ ,, s ◅ (V-wrap V)
step p ((s , unwrap-) ◅ V-wrap V)         = _ ,, _ ,, p ,, _ ,, s ◅ V
step p (□ V)                              = _ ,, _ ,, p ,, _ ,, □ V
step {Γ = Γ} p (◆ Γ' A)                   = _ ,, _ ,, p ,, _ ,, ◆ Γ' A
```

```
open import Data.Nat
open import Data.Maybe

stepper : ℕ → ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{T : Φ ⊢Nf⋆ *}{H : Φ' ⊢Nf⋆ *}
  → NoVar Γ'
  → State Γ T Γ' H
  → Σ Ctx⋆ λ Φ'
  → Σ (Ctx Φ') λ Γ'
  → NoVar Γ'
  × Σ (Φ' ⊢Nf⋆ *) λ H
  → Maybe (State Γ T Γ' H)
stepper zero {Γ' = Γ'}{H = H} p st = _ ,, Γ' ,, p ,, H ,, nothing 
stepper (suc n) p st with step p st
stepper (suc n) p st | Φ ,, Γ ,, q ,, _ ,, (s ▻ M) = stepper n q (s ▻ M)
stepper (suc n) p st | Φ ,, Γ ,, q ,, _ ,, (s ◅ V) = stepper n q (s ◅ V)
stepper (suc n) p st | Φ ,, Γ ,, q ,, _ ,, (□ V)   = Φ ,, Γ ,, q ,, _ ,, just (□ V)
stepper (suc n) p st | Φ ,, _ ,, q ,, _ ,, ◆ Γ' A     = Φ ,, Γ' ,, q ,, _ ,, just (◆ Γ' A)
```

This is the property I would like to have, but it cannot be proved directly like this:

```
open import Relation.Binary.PropositionalEquality

{-
preservation : ∀ n {Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(p : NoVar Γ)(t : Γ ⊢ A)
  → Σ (Φ ⊢Nf⋆ *) λ A' → Σ (Γ ⊢ A') λ t' → Σ (Value t') λ v → stepper n p (ε ▻ t) ≡ (Φ ,, Γ ,, p ,, just (□ v)) → A ≡ A'
-}
```
