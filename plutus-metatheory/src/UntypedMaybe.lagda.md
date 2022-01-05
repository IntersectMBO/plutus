```
{-# OPTIONS --type-in-type #-}
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
open import Untyped hiding (_⊢;extricateU;scopeCheckU) public
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

```
data Value : Set
data Env : Set → Set where
  [] : Env ⊥
  _∷_ : ∀{X} → Env X → Value → Env (Maybe X)
  
data Value where
  V-ƛ : ∀{X} → Env X → Maybe X ⊢ → Value
  V-con : TermCon → Value
  V-delay : ∀{X} → Env X → X ⊢ → Value

Ren : Set → Set → Set
Ren X Y = X → Y

lift : {X Y : Set} → Ren X Y → Ren (Maybe X) (Maybe Y)
lift ρ nothing = nothing
lift ρ (just x) = just (ρ x)

ren : {X Y : Set} → Ren X Y → X ⊢ → Y ⊢
ren ρ (` x)       = ` (ρ x)
ren ρ (ƛ t)       = ƛ (ren (lift ρ) t)
ren ρ (t · u)     = ren ρ t · ren ρ u
ren ρ (force t)   = force (ren ρ t)
ren ρ (delay t)   = delay (ren ρ t)
ren ρ (con tcn)   = con tcn
ren ρ (builtin b) = builtin b
ren ρ error       = error

weaken : {X : Set} → X ⊢ → Maybe X ⊢
weaken t = ren just t

Sub : Set → Set → Set
Sub X Y = X → Y ⊢

lifts : {X Y : Set} → Sub X Y → Sub (Maybe X) (Maybe Y)
lifts ρ nothing = ` nothing
lifts ρ (just x) = ren just (ρ x)

sub    : {X Y : Set} → Sub X Y → X ⊢ → Y ⊢
sub σ (` x)       = σ x
sub σ (ƛ t)       = ƛ (sub (lifts σ) t) 
sub σ (t · u)     = sub σ t · sub σ u
sub σ (force t)   = force (sub σ t)
sub σ (delay t)   = delay (sub σ t)
sub σ (con tcn)   = con tcn
sub σ (builtin b) = builtin b
sub σ error       = error

env2sub : ∀{Γ} → Env Γ → Sub Γ ⊥

discharge : Value → ⊥ ⊢
discharge (V-ƛ ρ t)   = ƛ (sub (lifts (env2sub ρ)) t)
discharge (V-con c)   = con c
discharge (V-delay ρ t) = delay (sub (env2sub ρ) t)

env2sub (ρ ∷ v) nothing  = discharge v
env2sub (ρ ∷ v) (just x) = env2sub ρ x

data Frame : Set where
  -·  : ∀{Γ} → Env Γ → Γ ⊢ → Frame
  _·- : Value → Frame
  force- : Frame

data Stack : Set where
  ε : Stack
  _,_ : Stack → Frame → Stack

data State : Set where
  _;_▻_ : {X : Set} → Stack → Env X → X ⊢ → State
  _◅_   : Stack → Value → State
  □ : Value → State
  ◆ : State

-- lookup is the same as env2sub without the discharge
lookup : ∀{Γ} → Env Γ → Γ → Value
lookup (ρ ∷ v) nothing  = v
lookup (ρ ∷ v) (just x) = lookup ρ x


step : State → State
step (s ; ρ ▻ ` x)       = s ◅ lookup ρ x
step (s ; ρ ▻ ƛ t)       = s ◅ V-ƛ ρ t
step (s ; ρ ▻ (t · u))   = (s , -· ρ u) ; ρ ▻ t
step (s ; ρ ▻ force t)   = (s , force-) ; ρ ▻ t
step (s ; ρ ▻ delay t)   = s ◅ V-delay ρ t
step (s ; ρ ▻ con c)     = s ◅ V-con c
step (s ; ρ ▻ builtin b) = ◆
step (s ; ρ ▻ error)     = ◆
step (ε ◅ v)             = □ v
step ((s , -· ρ u) ◅ v)  = (s , (v ·-)) ; ρ ▻ u
step ((s , (V-ƛ ρ t ·-)) ◅ v) = s ; ρ ∷ v ▻ t
step ((s , (V-con _     ·-)) ◅ v) = ◆ -- constant in function position
step ((s , (V-delay _ _ ·-)) ◅ v) = ◆ -- delay in function position
step ((s , force-) ◅ V-ƛ _ _)   = ◆ -- lambda in delay position
step ((s , force-) ◅ V-con _)   = ◆ -- constant in delay position
step ((s , force-) ◅ V-delay ρ t) = step (s ; ρ ▻ t)

step (□ v)               = □ v
step ◆                   = ◆

open import Function
stepper : ℕ → (t : State) → Either RuntimeError (Maybe (⊥ ⊢))
stepper 0       s = inj₁ gasError
stepper (suc n) s with step s
... | (s ; ρ ▻ t) = stepper n (s ; ρ ▻ t)
... | (s ◅ v)     = stepper n (s ◅ v)
... | (□ v)       = inj₂ $ just (discharge v)
... | ◆           = inj₁ userError
