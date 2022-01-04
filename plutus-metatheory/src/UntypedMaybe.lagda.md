```
open import Utils
open import Builtin

data _⊢ (X : Set) : Set where
  `   : X → X ⊢
  ƛ   : Maybe X ⊢ → X ⊢
  _·_ : X ⊢ → X ⊢ → X ⊢
  force : X ⊢ → X ⊢
  delay : X ⊢ → X ⊢
  con : TermCon → X ⊢
  builtin : (b : Builtin) → X ⊢
  error : X ⊢
```

```
open import Untyped hiding (_⊢;extricateU)
open import Data.Nat

extG : {X : Set} → (X → ℕ) → Maybe X → ℕ
extG g (just x) = suc (g x)
extG g nothing  = 0

extricateU : {X : Set} → (X → ℕ) → X ⊢ → Untyped
extricateU g (` x)       = UVar (g x)
extricateU g (ƛ t)       = ULambda (extricateU (extG g) t)
extricateU g (t · u)     = UApp (extricateU g t) (extricateU g u)
extricateU g (force t)   = UForce (extricateU g t)
extricateU g (delay t)   = UDelay (extricateU g t)
extricateU g (con c)     = UCon c
extricateU g (builtin b) = UBuiltin b
extricateU g error       = UError

```
