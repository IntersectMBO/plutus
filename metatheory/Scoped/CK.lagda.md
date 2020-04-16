# CK machine

```
module Scoped.CK where
```

```
open import Function
open import Data.Bool using (Bool;true;false)
open import Data.String
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality using (refl;inspect;subst;sym;_≡_) renaming ([_] to [[_]])
open import Data.Unit

open import Type
open import Type.BetaNormal
open import Scoped
open import Scoped.Reduction hiding (step)
open import Builtin
open import Scoped.RenamingSubstitution
open import Relation.Nullary
open import Utils
```

```
open import Data.Vec hiding ([_])

data Frame : ∀{n n'} → Weirdℕ n → Weirdℕ n' → Set where
  -·_ : ∀{n}{i : Weirdℕ n} → ScopedTm i → Frame i i
  _·- : ∀{n}{i : Weirdℕ n}{t : ScopedTm i } → Value t → Frame i i

  -·⋆_ :  ∀ {n}{i : Weirdℕ n}(A : ScopedTy n) → Frame i i

  wrap- :  ∀{n} → ScopedTy n → ScopedTy n → {i : Weirdℕ n} → Frame i i
  unwrap- : ∀{n}{i : Weirdℕ n} → Frame i i

  builtin- : ∀{o o' o'' n}{i : Weirdℕ n} → Builtin → Vec (ScopedTy n) o
    → {tel : Tel i o'} → VTel o' i tel → Tel i o'' →  Frame i i

data Stack : ∀{n n'}(i : Weirdℕ n)(i' : Weirdℕ n') → Set where
  ε   : ∀{n}{i : Weirdℕ n} → Stack i i
  _,_ : ∀{n n' n''}{i : Weirdℕ n}{i' : Weirdℕ n'}{i'' : Weirdℕ n''}
    → Stack i i' → Frame i' i'' → Stack i i''

data State{n}(i : Weirdℕ n) : ∀{n'}(i' : Weirdℕ n') → Set where
  _▻_ : ∀{n'}{i' : Weirdℕ n'} → Stack i i' → ScopedTm i' → State i i'
  _◅_ : ∀{n'}{i' : Weirdℕ n'} → Stack i i' → {t : ScopedTm i'} →  Value t
    → State i i'
  □   : {t : ScopedTm i} →  Value t → State i i
  ◆   : ∀{n'}{i' : Weirdℕ n'} → State i i'

open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

-- this function, apart from making a step, also determines the contexts and provides a proof.
-- These things could be done seperately.

-- this could also be presented as a relation and then there would be more function rather like progress

open import Data.Nat

VTel-extend : ∀{o n}{i : Weirdℕ n} → {tel : Tel i o} → VTel o i tel → {t : ScopedTm i} → Value t → VTel (suc o) i (tel :< t)
VTel-extend {tel = []} vs {t} v = v ,, _
VTel-extend {tel = t' ∷ tel} (v' ,, vs) {t} v = v' ,, VTel-extend vs v

vtel-lem : ∀{m n}{i : Weirdℕ m}(p : 0 ≡ n) → VTel n i (subst (Tel i) p [])
vtel-lem refl = tt

step : ∀{n n'}{i : Weirdℕ n}{i' : Weirdℕ n'}
  → NoVar i' → State i i' → Σ ℕ λ n' → Σ (Weirdℕ n') λ i' → NoVar i' × State i i'
step p (s ▻ ` x)              = ⊥-elim (noVar p x)
step p (s ▻ Λ K L)          = _ ,, _ ,, p ,, (s ◅ V-Λ {K = K} L)
step p (s ▻ (L ·⋆ A))         = _ ,, _ ,, p ,, (s , (-·⋆ A)) ▻ L
step p (s ▻ ƛ A L)          = _ ,, _ ,, p ,, s ◅ V-ƛ A L
step p (s ▻ (L · M))          = _ ,, _ ,, p ,, (s , (-· M)) ▻ L
step p (s ▻ con cn)           = _ ,, _ ,, p ,, s ◅ V-con cn
  -- ^ why is i inferrable?

-- type telescope is full
step {i' = i'} p (s ▻ builtin bn (inj₁ (≤‴-refl ,, refl)) As ts) = _ ,, _ ,, p ,, (s ▻ builtin bn (inj₂ (refl ,, z≤‴n)) As ts)
-- type telescope is not full yet
step {i' = i'} p (s ▻ builtin bn (inj₁ (≤‴-step q ,, r)) As ts) = _ ,, _ ,, p ,, (s ◅ V-builtin⋆ bn q As)

-- term telescope is full
step {i' = i'} p (s ▻ builtin bn (inj₂ (q ,, ≤‴-refl)) As ts) with arity bn | inspect arity bn
-- (annoying special case for builtin with no args)
step {i' = i'} p (s ▻ builtin bn (inj₂ (refl ,, ≤‴-refl)) As ts)       | zero  | [[ eq ]] =
  _ ,, _ ,, p ,, (s ▻ BUILTIN bn As (subst (Tel _) (sym eq) []) (vtel-lem (sym eq)))
-- (case for builtin with at least one arg)
step {i' = i'} p (s ▻ builtin bn (inj₂ (refl ,, ≤‴-refl)) As (t ∷ ts)) | suc n | [[ eq ]] =
  _ ,, _ ,, p ,, ((s , builtin- bn As tt ts) ▻ t )
  
-- term telescope is not full
step {i' = i'} p (s ▻ builtin bn (inj₂ (refl ,, ≤‴-step r)) As ts) = _ ,, _ ,, p ,, (s ◅ V-builtin bn As r ts)

step {i' = i'} p (s ▻ error A)           = _ ,, i' ,, p ,, ◆
step p (s ▻ wrap pat arg L)   = _ ,, _ ,, p ,, (s , wrap- pat arg) ▻ L
step p (s ▻ unwrap L)         = _ ,, _ ,, p ,, (s , unwrap-) ▻ L
step p (ε ◅ V)                = _ ,, _ ,, p ,, □ V
step p ((s , (-· M)) ◅ V) = _ ,, _ ,, p ,, ((s , (V ·-)) ▻ M)
step p (_◅_ (s , (V-ƛ A L ·-)) {M} W)         = _ ,, _ ,, p ,, s ▻ (L [ M ])
step {i' = i'} p ((s , (V-Λ V ·-)) ◅ W)           = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (V-con tcn ·-)) ◅ W)         = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (V-wrap A B V ·-)) ◅ W)      = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-ƛ A' L) = _ ,, i' ,, p ,, ◆
step p ((s , (-·⋆ A)) ◅ V-Λ  t)  = _ ,, _ ,, p ,, s ▻ (t [ A ]⋆)
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-con tcn) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-wrap A' B V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-builtin b As q ts) = _ ,, i' ,, p ,, ◆
step p ((s , wrap- A B) ◅ V) = _ ,, _ ,, p ,, (s ◅ V-wrap A B V)

-- β-unwrap
step           p ((s , unwrap-) ◅ V-wrap A B V) = _ ,, _ ,, p ,, (s ◅ V)
-- error conditions
step {i' = i'} p ((s , unwrap-) ◅ V-builtin b q As ts) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-builtin⋆ b q As) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-ƛ A t) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-Λ V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-con tcn) = _ ,, i' ,, p ,, ◆

step p (□ V)                  = _ ,, _ ,, p ,, □ V
step {i' = i'} p ◆              = _ ,, i' ,, p ,, ◆

-- some builtin related cases
step {i' = i'} p (_◅_ (s , builtin- b As {tel} vtel []) {t} V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (V-builtin⋆ b q As ·-)) ◅ V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-builtin⋆ b q As) = _ ,, i' ,, p ,, ◆

step {i' = i'} p ((s , (V-builtin b As q ts ·-)) ◅ V) = _ ,, i' ,, p ,, ◆
step p (_◅_ (s , builtin- b As {tel} vtel (t' ∷ tel')) {t} V) =
  _ ,, _ ,, p ,, (s , builtin- b As { tel :< t } (VTel-extend vtel V) tel') ▻ t'
```

```
open import Utils
stepper : ℕ → ∀{n n'}{i : Weirdℕ n}{i' : Weirdℕ n'} → NoVar i' → State i i' → Σ ℕ λ n' → Σ (Weirdℕ n') λ i' → NoVar i' × Maybe (State i i')
stepper zero {i' = i'} p st = _ ,, i' ,, p ,, nothing 
stepper (suc n) p st with step p st
stepper (suc n) p st | Φ ,, i ,, q ,, (s ▻ M) = stepper n q (s ▻ M)
stepper (suc n) p st | Φ ,, i ,, q ,, (s ◅ V) = stepper n q (s ◅ V)
stepper (suc n) p st | Φ ,, i ,, q ,, (□ V)   = Φ ,, i ,, q ,, just (□ V)
stepper (suc n) p st | Φ ,, i ,, q ,, ◆       = Φ ,, i ,, q ,, just ◆
```
