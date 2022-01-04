```
open import Utils
open import Builtin
open import Scoped using (ScopeError;deBError)

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
open import Untyped hiding (_⊢;extricateU;scopeCheckU)
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

open import Data.Empty
extricateU0 : ⊥  ⊢ → Untyped
extricateU0 t = extricateU (λ()) t
```

```
extG' : {X : Set} → (ℕ → Either ScopeError X) → ℕ → Either ScopeError (Maybe X)
extG' g zero    = return nothing
extG' g (suc n) = fmap just (g n)

scopeCheckU : {X : Set}
            → (ℕ → Either ScopeError X) → Untyped → Either ScopeError (X ⊢)
scopeCheckU g (UVar x)     = fmap ` (g x)
scopeCheckU g (ULambda t)  = fmap ƛ (scopeCheckU (extG' g) t)
scopeCheckU g (UApp t u)   = do
  t ← scopeCheckU g t
  u ← scopeCheckU g u
  return (t · u)
scopeCheckU g (UCon c)     = return (con c)
scopeCheckU g UError       = return error
scopeCheckU g (UBuiltin b) = return (builtin b)
scopeCheckU g (UDelay t)   = fmap delay (scopeCheckU g t)
scopeCheckU g (UForce t)   = fmap force (scopeCheckU g t)

scopeCheckU0 : Untyped → Either ScopeError (⊥ ⊢)
scopeCheckU0 t = scopeCheckU (λ _ → inj₁ deBError) t
```
