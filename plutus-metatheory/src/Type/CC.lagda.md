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

focusEvalCtx' : EvalCtx K J → EvalCtx J I → EvalCtx K I
focusEvalCtx' E [] = E
focusEvalCtx' E (x ·r E') = focusEvalCtx' (focusEvalCtx E (x ·r [])) E'
focusEvalCtx' E (E' l· x) = focusEvalCtx' (focusEvalCtx E ([] l· x)) E'
focusEvalCtx' E (x ⇒r E') = focusEvalCtx' (focusEvalCtx E (x ⇒r [])) E'
focusEvalCtx' E (E' l⇒ x) = focusEvalCtx' (focusEvalCtx E ([] l⇒ x)) E'
focusEvalCtx' E (μr x E') = focusEvalCtx' (focusEvalCtx E (μr x [])) E'
focusEvalCtx' E (μl E' B) = focusEvalCtx' (focusEvalCtx E (μl [] B)) E'
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
helper : {A : ∅ ⊢⋆ J}(V : Value⋆ A)
       → K ≡ J ⊎ Σ Kind (λ I → EvalCtx K I × Frame I J)
       → ∃ (State K)
helper V (inj₁ refl) = -, □ V
helper V (inj₂ (_ , E' , -· B)) = -, focusEvalCtx' E' (V ·r [])  ▻ B
helper V (inj₂ (_ , E' , (V-ƛ N ·-))) = -, E' ▻ (N [ discharge V ])
helper V (inj₂ (_ , E' , -⇒ B)) = -, focusEvalCtx' E' (V ⇒r [])  ▻ B
helper V (inj₂ (_ , E' , W ⇒-)) = -, E' ◅ (W V-⇒ V)
helper V (inj₂ (_ , E' , μ- B)) = -, focusEvalCtx' E' (μr V []) ▻ B
helper V (inj₂ (_ , E' , μ W -)) = -, E' ◅ V-μ W V

step : State K J → ∃ λ J' → State K J'
step (E ▻ Π A)                      = -, E ◅ V-Π A
step (E ▻ (A ⇒ B))                  = -, focusEvalCtx' E ([] l⇒ B)  ▻ A
step (E ▻ ƛ A)                      = -, E ◅ V-ƛ A
step (E ▻ (A · B))                  = -, focusEvalCtx' E ([] l· B) ▻ A
step (E ▻ μ A B)                    = -, focusEvalCtx' E (μl [] B) ▻ A
step (E ▻ con c)                    = -, E ◅ V-con c
step (□ V)                          = -, □ V
-- v we look at the E to decide what to do...
step (E ◅ V) = helper V (dissect E)
```

```
variable I' : Kind

data _-→s_ : State K J → State K I → Set where
  base  : {s : State K J}
        → s -→s s
  step* : {s : State K J}{s' : State K I}{s'' : State K I'}
        → step s ≡ (I , s')
        → s' -→s s''
        → s -→s s''

step** : {s : State K J}{s' : State K I}{s'' : State K I'}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

-- some high level structure of the reduction to CC machine below
{-
lemV : (A : ∅ ⊢⋆ J)(V : Value⋆ A)(E : EvalCtx K J) → (E ▻ A) -→s (E ◅ V)
lemV A V p = {!!}

lem62 : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ~ E' ⟦ A ⟧
      → (E ▻ B) -→s (focusEvalCtx' E E' ▻ A)
lem62 A .A E [] (~[] .A) = base
lem62 A .(_ · B) E (x₁ ·r E') (~·r .A .x₁ B .E' x) = step* refl (step** (lemV _ x₁ (focusEvalCtx E ([] l· B))) (step* refl {!lem62 A B (focusEvalCtx E (x₁ ·r [])) E' x!} ))
lem62 A B E (E' l· x₁) x = {!!}
lem62 A B E (x₁ ⇒r E') x = {!!}
lem62 A B E (E' l⇒ x₁) x = {!!}
lem62 A B E (μr x₁ E') x = {!!}
lem62 A B E (μl E' B₁) x = {!!}

lem1 : (A : ∅ ⊢⋆ J)(B : ∅ ⊢⋆ K)(E : EvalCtx K J)
       (A' : ∅ ⊢⋆ J)(B' : ∅ ⊢⋆ K)(E' : EvalCtx K J)
  → B ~ E ⟦ A ⟧ → B' ~ E' ⟦ A' ⟧ → B —→⋆ B' -> (E ▻ A) -→s (E' ▻ A')
lem1 A B E A' B' E' p q r = {!!}

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ~ E ⟦ A ⟧ → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind = {!!}


-- thm2 follows from this stronger theorem
thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ~ E ⟦ A ⟧ → (B : ∅ ⊢⋆ K)(V : Value⋆ B) → A' —↠⋆ B -> (E ▻ A) -→s ([] ◅ V)
thm1 A A' E p B V q = {!!}

-- this is the result we want
thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠⋆ B -> ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] (~[] A) B V p
-}
```
