# CK machine

```
module Scoped.CK where
```

```
open import Function

open import Type
open import Type.BetaNormal
open import Scoped
open import Scoped.Reduction hiding (step)
open import Builtin
open import Scoped.RenamingSubstitution
open import Data.String
open import Relation.Nullary
```

```
open import Data.List hiding ([_])

data Frame : ∀{n n'} → Weirdℕ n → Weirdℕ n' → Set where
  -·_ : ∀{n}{i : Weirdℕ n} → ScopedTm i → Frame i i
  _·- : ∀{n}{i : Weirdℕ n}{t : ScopedTm i } → Value t → Frame i i

  -·⋆_ :  ∀ {n}{i : Weirdℕ n}(A : ScopedTy n) → Frame i i

  wrap- :  ∀{n} → ScopedTy n → ScopedTy n → {i : Weirdℕ n} → Frame i i
  unwrap- : ∀{n}{i : Weirdℕ n} → Frame i i

  builtin- : ∀{n}{i : Weirdℕ n} → Builtin → List (ScopedTy n)
    → {tel : Tel i} → VTel i tel → Tel i →  Frame i i

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

VTel-extend : ∀{n}{i : Weirdℕ n} → {tel : Tel i} → VTel i tel → {t : ScopedTm i} → Value t → VTel i (tel Data.List.++ Data.List.[ t ])
VTel-extend {tel = []} vs {t} v = v ,, _
VTel-extend {tel = x ∷ tel} (v' ,, vs) {t} v = v' ,, VTel-extend vs v

step : ∀{n n'}{i : Weirdℕ n}{i' : Weirdℕ n'}
  → NoVar i' → State i i' → Σ ℕ λ n' → Σ (Weirdℕ n') λ i' → NoVar i' × State i i'
step p (s ▻ ` x)              = ⊥-elim (noVar p x)
step p (s ▻ Λ K L)          = _ ,, _ ,, p ,, (s ◅ V-Λ {K = K} L)
step p (s ▻ (L ·⋆ A))         = _ ,, _ ,, p ,, (s , (-·⋆ A)) ▻ L
step p (s ▻ ƛ A L)          = _ ,, _ ,, p ,, s ◅ V-ƛ A L
step p (s ▻ (L · M))          = _ ,, _ ,, p ,, (s , (-· M)) ▻ L
step p (s ▻ con cn)           = _ ,, _ ,, p ,, s ◅ V-con cn
  -- ^ why is i inferrable?
step {i' = i'} p (s ▻ error A)           = _ ,, i' ,, p ,, ◆
step p (s ▻ builtin bn As []) with arity bn Data.Nat.≟ 0
... | yes q = _ ,, _ ,, p ,, (s ▻ BUILTIN bn As [] _)
... | no  q = _ ,, _ ,, p ,, (s ◅ V-builtin bn As [])
step p (s ▻ builtin bn As (t ∷ tel)) =
  _ ,, _ ,, p ,, (s , builtin- bn As {[]} _ tel) ▻ t
step p (s ▻ wrap pat arg L)   = _ ,, _ ,, p ,, (s , wrap- pat arg) ▻ L
step p (s ▻ unwrap L)         = _ ,, _ ,, p ,, (s , unwrap-) ▻ L
step p (ε ◅ V)                = _ ,, _ ,, p ,, □ V
step p ((s , (-· M)) ◅ V) = _ ,, _ ,, p ,, ((s , (V ·-)) ▻ M)
step p (_◅_ (s , (V-ƛ A L ·-)) {M} W)         = _ ,, _ ,, p ,, s ▻ (L [ M ])
step {i' = i'} p ((s , (V-Λ V ·-)) ◅ W)           = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (V-con tcn ·-)) ◅ W)         = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (V-wrap A B V ·-)) ◅ W)      = _ ,, i' ,, p ,, ◆
step {i' = i'} p (_◅_ (s , (V-builtin b As tel ·-)) {t} W) =
  _ ,, i' ,, p ,, (s ▻ builtin b As (tel Data.List.++ Data.List.[ t ]) )
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-ƛ A' L) = _ ,, i' ,, p ,, ◆
step p ((s , (-·⋆ A)) ◅ V-Λ  t)  = _ ,, _ ,, p ,, s ▻ (t [ A ]⋆)
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-con tcn) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-wrap A' B V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , (-·⋆ A)) ◅ V-builtin b As ts) = _ ,, i' ,, p ,, ◆
step p ((s , wrap- A B) ◅ V) = _ ,, _ ,, p ,, (s ◅ V-wrap A B V)
step {i' = i'} p ((s , unwrap-) ◅ V-ƛ A t) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-Λ V) = _ ,, i' ,, p ,, ◆
step {i' = i'} p ((s , unwrap-) ◅ V-con tcn) = _ ,, i' ,, p ,, ◆
step p ((s , unwrap-) ◅ V-wrap A B V) = _ ,, _ ,, p ,, (s ◅ V)
step {i' = i'} p ((s , unwrap-) ◅ V-builtin b As ts) = _ ,, i' ,, p ,, ◆
step p (□ V)                  = _ ,, _ ,, p ,, □ V
step {i' = i'} p ◆              = _ ,, i' ,, p ,, ◆
step p (_◅_ (s , builtin- b As {tel} vtel []) {t} V) with arity b Data.Nat.≟ Data.List.length tel + 1
... | yes q = _ ,, _ ,, p ,, (s ▻ BUILTIN b As (tel Data.List.++ Data.List.[ t ]) (VTel-extend vtel V))
... | no q = _ ,, _ ,, p ,, (s ◅ V-builtin b As (tel Data.List.++ Data.List.[ t ]))
 -- check for length here and return V-builtin if not?

step p (_◅_ (s , builtin- b As {tel} vtel (t' ∷ tel')) {t} V) =
  _ ,, _ ,, p ,, (s , builtin- b As {tel Data.List.++ Data.List.[ t ]} (VTel-extend vtel V) tel') ▻ t'
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
