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

## Frames

A frame corresponds to a type with a hole in it for a missing sub
type. It is indexed by two kinds. The first index is the kind of the
outer type that the frame corresponds to, the second index refers to
the kind of the missing subterm. The frame datatypes has constructors
for all the different places in a type that we might need to make a
hole.

```
data Frame : Kind → Kind → Set where
  -·_     : ∅ ⊢⋆ K → Frame J (K ⇒ J)
  _·-     : {A : ∅ ⊢⋆ K ⇒ J} → Value⋆ A → Frame J K
  -⇒_     : ∅ ⊢⋆ * → Frame * *
  _⇒-     : {A : ∅ ⊢⋆ *} → Value⋆ A → Frame * *
  μ-_     : (B : ∅ ⊢⋆ K) → Frame * ((K ⇒ *) ⇒ K ⇒ *)
  μ_-     : {A : ∅ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *} → Value⋆ A → Frame * K
```

Given a frame and type to plug in to it we can close the frame and
recover a type with no hole. By indexing frames by kinds we can
specify exactly what kind the plug needs to have and ensure we don't
plug in something of the wrong kind. We can also ensure what kind the
returned type will have.

```
closeFrame : Frame K J → ∅ ⊢⋆ J → ∅ ⊢⋆ K
closeFrame (-· B)  A = A · B
closeFrame (_·- A) B = discharge A · B
closeFrame (-⇒ B)  A = A ⇒ B
closeFrame (_⇒- A) B = discharge A ⇒ B
closeFrame (μ_- A) B = μ (discharge A) B
closeFrame (μ- B)  A = μ A B
```

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
  -- ◆ : ∀ (J : Kind) →  State K J -- impossible in the type language
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
step (ε ◅ V)                        = -, □ V
step ((s , (-· B)) ◅ V)             = -, (s , V ·-) ▻ B
step (_◅_ (s , (V-ƛ A ·-)) B)       = -, s ▻ (A [ discharge B ])
step ((s , (-⇒ B)) ◅ V)             = -, (s , V ⇒-) ▻ B
step ((s , (V ⇒-)) ◅ W)             = -, s ◅ (V V-⇒ W)
step ((s , μ- B) ◅ A)               = -, (s , μ A -) ▻ B
step ((s , μ A -) ◅ B)              = -, s ◅ V-μ A B
step (□ V)                          = -, □ V
```
