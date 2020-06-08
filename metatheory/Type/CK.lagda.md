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
step (stack ▻ Π A) = _ , stack ◅ V-Π {N = A}
step (stack ▻ (A ⇒ B)) = _ , (stack , -⇒ B) ▻ A
step (stack ▻ ƛ A) = _ , stack ◅ V-ƛ {N = A}
step (stack ▻ (A · B)) = _ , (stack , -· B) ▻ A
step (stack ▻ μ1) = _ , stack ◅ N- N-μ1
step (stack ▻ con c) = _ , stack ◅ V-con {tcn = c}
step (ε ◅ V) = _ , □ V
step ((stack , (-· B)) ◅ V) = _ , (stack , V ·-) ▻ B
step (_◅_ (stack , (V-ƛ {N = A} ·-)) {A = B}  W) = _ , stack ▻ (A [ B ])
step ((stack , (N- N ·-)) ◅ W) = _ , stack ◅ N- (N-· N W)
step ((stack , (-⇒ B)) ◅ V) = _ , (stack , V ⇒-) ▻ B
step ((stack , (V ⇒-)) ◅ W) = _ , stack ◅ (V V-⇒ W)
step {K} (□ V) = K , □ V

--closing/unwinding things

closeFrame : ∀{K H} → Frame K H → ∅ ⊢⋆ H → ∅ ⊢⋆ K
closeFrame (-· B)          A = A · B
closeFrame (_·- {A = A} V) B = A · B
closeFrame (-⇒ B)          A = A ⇒ B
closeFrame (_⇒- {A = A} V) B = A ⇒ B

closeStack : ∀{K H} → Stack K H → ∅ ⊢⋆ H → ∅ ⊢⋆ K
closeStack ε           A = A
closeStack (stack , f) A = closeStack stack (closeFrame f A)

closeState : ∀{K H} → State K H → ∅ ⊢⋆ K
closeState (stack ▻ A)           = closeStack stack A
closeState (_◅_ stack {A = A} V) = closeStack stack A
closeState (□ {A = A} V)         = A
```

