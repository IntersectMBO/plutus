# CK machine

```
module Scoped.CK where
```

```
open import Function
open import Data.Bool using (Bool;true;false)
open import Data.Nat
open import Data.String
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality using (refl;inspect;subst;sym;_≡_;trans;cong) renaming ([_] to [[_]])
open import Data.Unit
open import Data.Nat using (_+_;suc)
open import Data.Nat.Properties
open import Type
open import Type.BetaNormal
open import Scoped
open import Scoped.Reduction hiding (step;trans;Error)
open import Builtin
open import Scoped.RenamingSubstitution
open import Relation.Nullary
open import Utils
```

```
open import Data.Vec hiding ([_])

data Frame : Set where
  -·_ : ScopedTm Z → Frame
  _·- : {t : ScopedTm Z} → Value t → Frame

  -·⋆_ :  (A : ScopedTy 0) → Frame

  wrap- :  ScopedTy 0 → ScopedTy 0 → Frame
  unwrap- : Frame

data Stack : Set where
  ε   : Stack
  _,_ : Stack → Frame → Stack

data State : Set where
  _▻_ : Stack → ScopedTm Z → State
  _◅_ : Stack → {t : ScopedTm Z} → Value t → State
  □   : {t : ScopedTm Z} →  Value t → State
  ◆   : State

open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

-- this function, apart from making a step, also determines the
-- contexts and provides a proof.  These things could be done
-- seperately.

-- this could also be presented as a relation and then there would be
-- more function rather like progress

step : State → State
step (s ▻ Λ K L)    = s ◅ V-Λ {K = K} L
step (s ▻ (L ·⋆ A)) = (s , (-·⋆ A)) ▻ L
step (s ▻ ƛ A L)    = s ◅ V-ƛ A L
step (s ▻ (L · M))  = (s , (-· M)) ▻ L
step (s ▻ con cn)   = s ◅ V-con cn
step (s ▻ error A) = ◆
step (s ▻ wrap pat arg L) = (s , wrap- pat arg) ▻ L
step (s ▻ unwrap L) = (s , unwrap-) ▻ L
step (s ▻ ibuiltin b) = s ◅ ival b
step (ε ◅ V) = □ V
step ((s , (-· M)) ◅ V) = (s , (V ·-)) ▻ M
step (_◅_ (s , (V-ƛ A L ·-)) {M} W) = s ▻ (L [ M ])
step ((s , (V-builtin b t p q base vs ·-)) ◅ V) =
  s ▻ IBUILTIN' b p q (vs , _ , V) 
step ((s , (V-builtin b t p q (skipT r) vs ·-)) ◅ V) =
  s ◅ V-builtin⋆ b (t · deval V) p q r (vs , _ , V)
step ((s , (V-builtin b t p q (skipS r) vs ·-)) ◅ V) =
  s ◅ V-builtin b (t · deval V) p q r (vs , _ , V)
step ((s , (V-Λ V ·-)) ◅ W) = ◆
step ((s , (V-con tcn ·-)) ◅ W) = ◆
step ((s , (V-wrap A B V ·-)) ◅ W) = ◆
step ((s , (V-builtin⋆ b t p q r vs ·-)) ◅ V) = ◆

step ((s , (-·⋆ A)) ◅ V-Λ  t)  = s ▻ (t [ A ]⋆)
step ((s , (-·⋆ A)) ◅ V-builtin⋆ b t p q base vs) = s ▻ IBUILTIN' b p q vs
step ((s , (-·⋆ A)) ◅ V-builtin⋆ b t p q (skipT r) vs) =
  s ◅ V-builtin⋆ b (t ·⋆ A) p q r vs
step ((s , (-·⋆ A)) ◅ V-builtin⋆ b t p q (skipS r) vs) =
  s ◅ V-builtin b (t ·⋆ A) p q r vs
step ((s , wrap- A B) ◅ V) = s ◅ V-wrap A B V
step ((s , (-·⋆ A)) ◅ V-ƛ A' L) = ◆
step ((s , (-·⋆ A)) ◅ V-con tcn) = ◆
step ((s , (-·⋆ A)) ◅ V-wrap A' B V) = ◆
step ((s , (-·⋆ A)) ◅ V-builtin b t p q r vs) = ◆

step ((s , unwrap-) ◅ V-wrap A B V) = s ◅ V
step ((s , unwrap-) ◅ V-builtin a b c d e f) = ◆
step ((s , unwrap-) ◅ V-builtin⋆ a b c d e f) = ◆
step ((s , unwrap-) ◅ V-ƛ A t) = ◆
step ((s , unwrap-) ◅ V-Λ V) = ◆
step ((s , unwrap-) ◅ V-con tcn) = ◆

step (□ V) = □ V
step ◆     = ◆

discharge : {t : ScopedTm Z} → Value t → ScopedTm Z
discharge {t} _ = t
```

```
open import Utils
stepper : ℕ → State → Either RuntimeError State
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | s ▻ M = stepper n (s ▻ M)
stepper (suc n) st | s ◅ V = stepper n (s ◅ V)
stepper (suc n) st | □ V   = return (□ V)
stepper (suc n) st | ◆     = return ◆
```
