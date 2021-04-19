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
open import Type.ReductionC hiding (step)

open import Data.Product
```

The CK machine is an abstract machine used to compute a lambda term to
a value. Here we use it on types.

The CK machine operates on a type by focussing on a subexpression
(subtype) of that type and computing it step-by-step until it becomes
a value. When the subtype becomes a value it searches outwards for the
next subexpression to compute and then carries on until no further
computation is necessary. It keeps track of the context using `Frame`s
to track the relationship between a subtype the immediate ancestor
type that contains it (e.g., `- · B` is a frame corresponding to an
application where the function term `A` is missing).  `Stack`s to
represent paths to missing subtypes deep in a type, and a `State` to
track the necessary changes of mode during execution.

Our CK machine is intrinsically kinded. The step function, which
performs one step of computation, preserves the kind of the overall
type and the intermediate data structures are indexed by kinds to
enable this.

## Stack

A stack is a sequence of frames. It allows us to specify a single hole
deep in a type or one can think of it as a path from the root of the
type to a single hole somewhere deep inside the type.

```
data Stack (K : Kind) : Kind → Set where
  ε   : Stack K K
  _,_ : Stack K J → Frame J I → Stack K I
```

Analogously to frames we can close a stack by plugging in a type of
appropriate kind.

```
closeStack : Stack K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeStack ε       A = A
closeStack (s , f) A = closeStack s (closeFrame f A)
```

## State

There are three state of our type CK machine. In state `▻` we have a
stack and a subtype in focus that we requires further computation. In
state `◅` the subtype in focus is a value and no further computation
on it is necessary or possible, so we must change direction and look
to the stack for what to do next. In state `□` we have compute the
outer type to a value so we are done. We do not need an error state
`◆`. The type language does not have any effects or errors so the CK
machine cannot encounter an error when processing a well-kinded
type. This CK machine only operates on well-kinded types so no runtime
kind errors are possible either.

```
data State (K : Kind) : Kind → Set where
  _▻_ : Stack K J → ∅ ⊢⋆ J → State K J
  _◅_ : Stack K J → {A : ∅ ⊢⋆ J} → Value⋆ A → State K J
  □   : {A : ∅ ⊢⋆ K} →  Value⋆ A → State K K
```

Analogously to `Frame` and `Stack` we can also close a `State`:

```
closeState : State K J → ∅ ⊢⋆ K
closeState (s ▻ A)   = closeStack s A
closeState (_◅_ s A) = closeStack s (discharge A)
closeState (□ A)     = discharge A
```

## The machine

The `step` function performs one step of computation. It takes a state
and return a new state. The kind index `K` refers to the kind of the
outer type which is preserved. The second index `J/J'` refers to the
kind of the subtype in focus which may change.

```
step : State K J → ∃ λ J' → State K J'
step (s ▻ Π A)                      = -, s ◅ V-Π A
step (s ▻ (A ⇒ B))                  = -, (s , -⇒ B) ▻ A
step (s ▻ ƛ A)                      = -, s ◅ V-ƛ A
step (s ▻ (A · B))                  = -, (s , -· B) ▻ A
step (s ▻ μ A B)                    = -, (s , μ- B) ▻ A
step (s ▻ con c)                    = -, s ◅ V-con c
step (ε ◅ V)                        = -, (ε ◅ V)
step ((s , (-· B)) ◅ V)             = -, (s , V ·-) ▻ B
step ((s , (V-ƛ A ·-)) ◅ B)       = -, s ▻ (A [ discharge B ])
step ((s , (-⇒ B)) ◅ V)             = -, (s , V ⇒-) ▻ B
step ((s , (V ⇒-)) ◅ W)             = -, s ◅ (V V-⇒ W)
step ((s , μ- B) ◅ A)               = -, (s , μ A -) ▻ B
step ((s , μ A -) ◅ B)              = -, s ◅ V-μ A B
step (□ V)                          = -, □ V
```

reflexive transitive closure of step:

```
open import Relation.Binary.PropositionalEquality

data _-→ck_ : State K J → State K I → Set where
  base  : {s : State K J}
        → s -→ck s
  step* : {s : State K J}{s' : State K I}{s'' : State K I'}
        → step s ≡ (I , s')
        → s' -→ck s''
        → s -→ck s''

step** : {s : State K J}{s' : State K I}{s'' : State K I'}
        → s -→ck s'
        → s' -→ck s''
        → s -→ck s''
step** base q = q
step** (step* x p) q = step* x (step** p q)
```

```
change-dir : (s : Stack I J)(A : ∅ ⊢⋆ J) (V : Value⋆ A) → (s ▻ A) -→ck (s ◅ V)
change-dir s .(Π N) (V-Π N) = step* refl base
change-dir s .(_ ⇒ _) (V V-⇒ V₁) = step* refl (step** (change-dir _ _ V) (step* refl (step** (change-dir _ _ V₁) (step* refl base))))
change-dir s .(ƛ N) (V-ƛ N) = step* refl base
change-dir s .(con tcn) (V-con tcn) = step* refl base
change-dir s .(μ _ _) (V-μ V V₁) = step* refl (step** (change-dir _ _ V) (step* refl (step** (change-dir _ _ V₁) (step* refl base))))

subst-step* : {s : State K J}{s' : State K J'}{s'' : State K I}
        → _≡_ {A = Σ Kind (State K)} (J , s) (J' , s')
        → s' -→ck s''
        → s -→ck s''
subst-step* refl q = q
```

Converting from evaluation contexts to stacks of frames:

```
open import Data.Sum
open import Type.ReductionC
import Type.CC as CC


{-# TERMINATING #-}
helper : ∀{E} → ((Σ (K ≡ J) λ p → subst (λ K → EvalCtx K J) p E ≡ []) ⊎ (Σ Kind λ I → EvalCtx K I × Frame I J)) → Stack K J

EvalCtx2Stack : ∀ {I J} → EvalCtx I J → Stack I J
EvalCtx2Stack E = helper (dissect' E)

helper (inj₁ (refl , refl)) = ε
helper (inj₂ (I , E , F)) = EvalCtx2Stack E , F

lemmaH : (E : EvalCtx K J)(F : Frame J I)
  → (helper (dissect' E) , F) ≡ helper (dissect' (extendEvalCtx E F))
lemmaH E F rewrite CC.lemma' E F = refl


Stack2EvalCtx : ∀ {I J} → Stack I J → EvalCtx I J
Stack2EvalCtx ε       = []
Stack2EvalCtx (s , F) = extendEvalCtx (Stack2EvalCtx s) F

cc2ck : ∀ {I J} → CC.State I J → State I J
cc2ck (x CC.▻ x₁) = EvalCtx2Stack x ▻ x₁
cc2ck (x CC.◅ x₁) = EvalCtx2Stack x ◅ x₁
cc2ck (CC.□ x) = □ x

ck2cc : ∀ {I J} → State I J → CC.State I J
ck2cc (x ▻ x₁) = Stack2EvalCtx x CC.▻ x₁
ck2cc (x ◅ x₁) = Stack2EvalCtx x CC.◅ x₁
ck2cc (□ x) = CC.□ x


thm64 : (s : CC.State K J)(s' : CC.State K J')
  → s CC.-→s s' → cc2ck s -→ck cc2ck s'
thm64 s .s CC.base = base
thm64 (x CC.▻ Π x₁) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (x CC.▻ (x₁ ⇒ x₂)) s' (CC.step* refl p) =
  step* refl (subst-step* (cong (λ s → * , s ▻ x₁) (lemmaH x (-⇒ x₂))) (thm64 _ s' p))
thm64 (x CC.▻ ƛ x₁) s' (CC.step* refl p) = step* refl (thm64 _ s' p)
thm64 (x CC.▻ (x₁ · x₂)) s' (CC.step* refl p) =
  step* refl (subst-step* (cong (λ s → _ , s ▻ x₁) (lemmaH x (-· x₂))) (thm64 _ s' p))
thm64 (x CC.▻ μ x₁ x₂) s' (CC.step* refl p) =
  step* refl (subst-step* (cong (λ s → _ , s ▻ x₁) (lemmaH x (μ- x₂))) (thm64 _ s' p))
thm64 (x CC.▻ con x₁) s' (CC.step* refl p) =
  step* refl (thm64 _ s' p)
thm64 (x CC.◅ x₁) s' (CC.step* refl p) with dissect' x | inspect dissect' x
... | inj₁ (refl , refl) | [ eq ] = step* refl (thm64 _ s' p)
... | inj₂ (I , E , (-· x₂)) | [ eq ] rewrite dissect'-lemma x E (-· x₂) eq | CC.lemma E (-· x₂) = step* refl (subst-step* (cong (λ E  → _ , E ▻ x₂) (lemmaH E (x₁ ·-))) (thm64 _ s' p))
... | inj₂ (I , E , (V-ƛ x₂ ·-)) | [ eq ] rewrite dissect'-lemma x E (V-ƛ x₂ ·-) eq | CC.lemma E (V-ƛ x₂ ·-) = step* refl (thm64 _ s' p)
... | inj₂ (.* , E , (-⇒ x₂)) | [ eq ] rewrite dissect'-lemma x E (-⇒ x₂) eq | CC.lemma E (-⇒ x₂)
  = step* refl (subst-step* (cong (λ E → _ , E ▻ x₂) (lemmaH E (x₁ ⇒-))) (thm64 _ s' p))
... | inj₂ (.* , E , (x₂ ⇒-)) | [ eq ] rewrite dissect'-lemma x E (x₂ ⇒-) eq | CC.lemma E (x₂ ⇒-) = step* refl (thm64 _ s' p)
... | inj₂ (.* , E , (μ- B)) | [ eq ] rewrite dissect'-lemma x E (μ- B) eq | CC.lemma E (μ- B)
  = step* refl (subst-step* (cong (λ E → _ , E ▻ B) (lemmaH E (μ x₁ -))) (thm64 _ s' p))
... | inj₂ (.* , E , μ x₂ -) | [ eq ]  rewrite dissect'-lemma x E (μ x₂ -) eq | CC.lemma E (μ x₂ -) = step* refl (thm64 _ s' p)
thm64 (CC.□ x) s' (CC.step* refl p) = step* refl (thm64 _ s' p)

thm64b : (s : State K J)(s' : State K J')
  → s -→ck s' → ck2cc s CC.-→s ck2cc s'
thm64b s .s base = CC.base
thm64b (s ▻ Π A) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (s ▻ (A ⇒ B)) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (s ▻ ƛ A) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (s ▻ (A · B)) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (s ▻ μ A B) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (s ▻ con c) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b (ε ◅ V) s' (step* refl q) = CC.step* refl (thm64b _ _ q)
thm64b ((s , (-· B)) ◅ V) s' (step* refl q) =
  CC.step* (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) (-· B)))
           (thm64b _ _ q)
thm64b ((s , (V-ƛ A ·-)) ◅ V) s' (step* refl q) = CC.step*
  (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) (_ ·-)))
  (thm64b _ _ q)
thm64b ((s , (-⇒ B)) ◅ V) s' (step* refl q) = CC.step*
  (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) _))
  (thm64b _ _ q)
thm64b ((s , (VA ⇒-)) ◅ V) s' (step* refl q) = CC.step*
  (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) _))
  (thm64b _ _ q)

thm64b ((s , (μ- B)) ◅ V) s' (step* refl q) = CC.step*
  (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) _))
  (thm64b _ _ q)
thm64b ((s , μ VA -) ◅ V) s' (step* refl q) = CC.step*
  (cong (CC.stepV V) (CC.lemma (Stack2EvalCtx s) _))
  (thm64b _ _ q)
thm64b (□ V)   s' (step* refl q) = CC.step* refl (thm64b _ _ q)
```

