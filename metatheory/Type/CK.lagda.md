```
module Type.CK where

open import Type
open import Type.RenamingSubstitution
open import Type.Reduction hiding (step)

open import Data.Product

-- a CK machine for types

data Frame : (K : Kind)(H : Kind) → Set where
  -·_     : ∀{K J} → ∅ ⊢⋆ K → Frame J (K ⇒ J)
  _·-     : ∀{K J}{A : ∅ ⊢⋆ K ⇒ J} → Value⋆ A → Frame J K
  -⇒_     : ∅ ⊢⋆ * → Frame * *
  _⇒-     : {A : ∅ ⊢⋆ *} → Value⋆ A → Frame * *
data Stack (K : Kind) : (H : Kind) → Set where
  ε   : Stack K K
  _,_ : ∀{H1 H2}
    → Stack K H1
    → Frame H1 H2 → Stack K H2

data State (K : Kind) : (H : Kind) → Set where
  _▻_ : {H : Kind} → Stack K H → ∅ ⊢⋆ H → State K H
  _◅_ : {H : Kind} → Stack K H → {A : ∅ ⊢⋆ H} → Value⋆ A
    → State K H 
  □  : {A : ∅ ⊢⋆ K} →  Value⋆ A → State K K
  -- ◆   : ∀ (J : Kind) →  State K J -- impossible in the typed language

step : ∀{K H} → State K H → Σ Kind λ H' → State K H'
step (s ▻ Π A)                               = _ , s ◅ V-Π A
step (s ▻ (A ⇒ B))                           = _ , (s , -⇒ B) ▻ A
step (s ▻ ƛ A)                               = _ , s ◅ V-ƛ A
step (s ▻ (A · B))                           = _ , (s , -· B) ▻ A
step (s ▻ μ1)                                = _ , s ◅ N- N-μ1
step (s ▻ con c)                             = _ , s ◅ V-con c
step (ε ◅ V)                                 = _ , □ V
step ((s , (-· B)) ◅ V)                      = _ , (s , V ·-) ▻ B
step (_◅_ (s , (V-ƛ A ·-)) {A = B}  W)       = _ , s ▻ (A [ B ])
step ((s , (N- N ·-)) ◅ W)                   = _ , s ◅ N- (N-· N W)
step ((s , (-⇒ B)) ◅ V)                      = _ , (s , V ⇒-) ▻ B
step ((s , (V ⇒-)) ◅ W)                      = _ , s ◅ (V V-⇒ W)
step (□ V)                                   = _ , □ V

--closing/unwinding things

closeFrame : ∀{K H} → Frame K H → ∅ ⊢⋆ H → ∅ ⊢⋆ K
closeFrame (-· B)          A = A · B
closeFrame (_·- {A = A} V) B = A · B
closeFrame (-⇒ B)          A = A ⇒ B
closeFrame (_⇒- {A = A} V) B = A ⇒ B

closeStack : ∀{K H} → Stack K H → ∅ ⊢⋆ H → ∅ ⊢⋆ K
closeStack ε           A = A
closeStack (s , f) A = closeStack s (closeFrame f A)

closeState : ∀{K H} → State K H → ∅ ⊢⋆ K
closeState (s ▻ A)           = closeStack s A
closeState (_◅_ s {A = A} V) = closeStack s A
closeState (□ {A = A} V)         = A
```
