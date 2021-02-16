---
title: CC machine for types
layout: page
---

```
module Type.CC where
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Type.ReductionC hiding (step)

open import Data.Product
```

```
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum

-- expose the bottom inner layer of the evalctx
dissect : (E : EvalCtx K J) → K ≡ J ⊎ Σ Kind λ I → EvalCtx K I × Frame I J
dissect [] = inj₁ refl
dissect (V ·r E) with dissect E 
... | inj₁ refl = inj₂ (-, [] , V ·-)
... | inj₂ (_ , E' , f) = inj₂ (-, V ·r E' , f)
dissect (E l· B) with dissect E 
... | inj₁ refl = inj₂ (-, [] , -· B)
... | inj₂ (_ , E' , f) = inj₂ (-, E' l· B , f)
dissect (V ⇒r E) with dissect E
... | inj₁ refl = inj₂ (-, [] , V ⇒-)
... | inj₂ (_ , E' , f) = inj₂ (-, V ⇒r E' , f)
dissect (E l⇒ B) with dissect E
... | inj₁ refl = inj₂ (-, [] , -⇒ B)
... | inj₂ (_ , E' , f) = inj₂ (-, E' l⇒ B , f)
dissect (μr V E) with dissect E
... | inj₁ refl         = inj₂ (-, [] , μ V -)
... | inj₂ (_ , E' , f) = inj₂ (-, μr V E' , f)
dissect (μl E B) with dissect E
... | inj₁ refl = inj₂ (-, [] , μ- B)
... | inj₂ (_ , E' , f) = inj₂ (-, μl E' B , f)

-- this reaches down inside the evaluation context and changes the
-- scope of the hole
--
-- it could also take a frame instead of an evalctx as it's second arg
focusEvalCtx : EvalCtx K J → EvalCtx J I → EvalCtx K I
focusEvalCtx []       E' = E'
focusEvalCtx (V ·r E) E' = V ·r focusEvalCtx E E'
focusEvalCtx (E l· B) E' = focusEvalCtx E E' l· B
focusEvalCtx (V ⇒r E) E' = V ⇒r focusEvalCtx E E'
focusEvalCtx (E l⇒ B) E' = focusEvalCtx E E' l⇒ B
focusEvalCtx (μr V E) E' = μr V (focusEvalCtx E E')
focusEvalCtx (μl E B) E' = μl (focusEvalCtx E E') B
```

```
data State (K : Kind) : Kind → Set where
  _▻_ : EvalCtx K J → ∅ ⊢⋆ J → State K J
  _◅_ : EvalCtx K J  → {A : ∅ ⊢⋆ J} → Value⋆ A → State K J
  □   : {A : ∅ ⊢⋆ K} →  Value⋆ A → State K K
```

```
closeState : State K J → ∅ ⊢⋆ K
closeState (E ▻ A) = closeEvalCtx E A
closeState (E ◅ V) = closeEvalCtx E (discharge V)
closeState (□ A)   = discharge A
```


## The machine

The `step` function performs one step of computation. It takes a state
and return a new state. The kind index `K` refers to the kind of the
outer type which is preserved. The second index `J/J'` refers to the
kind of the subtype in focus which may change.

```
step : State K J → ∃ λ J' → State K J'
step (E ▻ Π A)                      = -, E ◅ V-Π A
step (E ▻ (A ⇒ B))                  = -, focusEvalCtx E ([] l⇒ B)  ▻ A
step (E ▻ ƛ A)                      = -, E ◅ V-ƛ A
step (E ▻ (A · B))                  = -, focusEvalCtx E ([] l· B) ▻ A
step (E ▻ μ A B)                    = -, focusEvalCtx E (μl [] B) ▻ A
step (E ▻ con c)                    = -, E ◅ V-con c
step (□ V)                          = -, □ V
step (E ◅ V) with dissect E
... | inj₁ refl = -, □ V
... | inj₂ (_ , E' , -· B) = -, focusEvalCtx E' (V ·r [])  ▻ B
... | inj₂ (_ , E' , (V-ƛ N ·-)) =
  -, E' ▻ (N [ discharge V ])
... | inj₂ (_ , E' , -⇒ B) = -, focusEvalCtx E' (V ⇒r [])  ▻ B
... | inj₂ (_ , E' , W ⇒-) = -, E' ◅ (W V-⇒ V)
... | inj₂ (_ , E' , μ- B) = -, focusEvalCtx E' (μr V []) ▻ B
... | inj₂ (_ , E' , μ W -) = -, E' ◅ V-μ W V
```
