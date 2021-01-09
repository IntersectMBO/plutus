---
title: CK machine for types
layout: page
---

```
module Type.CK where
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Type.Reduction hiding (step)

open import Data.Product
```

## Frames

```
data Frame : Kind → Kind → Set where
  -·_     : ∅ ⊢⋆ K → Frame J (K ⇒ J)
  _·-     : {A : ∅ ⊢⋆ K ⇒ J} → Value⋆ A → Frame J K
  -⇒_     : ∅ ⊢⋆ * → Frame * *
  _⇒-     : {A : ∅ ⊢⋆ *} → Value⋆ A → Frame * *
  μ-_     : (B : ∅ ⊢⋆ K) → Frame * ((K ⇒ *) ⇒ K ⇒ *)
  μ_-     : {A : ∅ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *} → Value⋆ A → Frame * K
```

## Stack

```
data Stack (K : Kind) : Kind → Set where
  ε   : Stack K K
  _,_ : Stack K J → Frame J I → Stack K I
```

## State

```
data State (K : Kind) : Kind → Set where
  _▻_ : Stack K J → ∅ ⊢⋆ J → State K J
  _◅_ : Stack K J → {A : ∅ ⊢⋆ J} → Value⋆ A → State K J
  □   : {A : ∅ ⊢⋆ K} →  Value⋆ A → State K K
  -- ◆ : ∀ (J : Kind) →  State K J -- impossible in the type language
```

## The machine

```
step : State K J → ∃ λ J' → State K J'
step (s ▻ Π A)                      = -, s ◅ V-Π A
step (s ▻ (A ⇒ B))                  = -, (s , -⇒ B) ▻ A
step (s ▻ ƛ A)                      = -, s ◅ V-ƛ A
step (s ▻ (A · B))                  = -, (s , -· B) ▻ A
step (s ▻ μ A B)                    = -, (s , μ- B) ▻ A
step (s ▻ con c)                    = -, s ◅ V-con c
step (ε ◅ V)                        = -, □ V
step ((s , (-· B)) ◅ V)             = -, (s , V ·-) ▻ B
step (_◅_ (s , (V-ƛ A ·-)) B)       = -, s ▻ (A [ discharge B ])
step ((s , (-⇒ B)) ◅ V)             = -, (s , V ⇒-) ▻ B
step ((s , (V ⇒-)) ◅ W)             = -, s ◅ (V V-⇒ W)
step ((s , μ- B) ◅ A)               = -, (s , μ A -) ▻ B
step ((s , μ A -) ◅ B)              = -, s ◅ V-μ A B
step (□ V)                          = -, □ V
```

## Closing Frames and Unwinding Stacks

```
closeFrame : Frame K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeFrame (-· B)  A = A · B
closeFrame (_·- A) B = discharge A · B
closeFrame (-⇒ B)  A = A ⇒ B
closeFrame (_⇒- A) B = discharge A ⇒ B
closeFrame (μ_- A) B = μ (discharge A) B
closeFrame (μ- B)  A = μ A B

closeStack : Stack K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeStack ε       A = A
closeStack (s , f) A = closeStack s (closeFrame f A)

closeState : State K J → ∅ ⊢⋆ K
closeState (s ▻ A)   = closeStack s A
closeState (_◅_ s A) = closeStack s (discharge A)
closeState (□ A)     = discharge A
```
