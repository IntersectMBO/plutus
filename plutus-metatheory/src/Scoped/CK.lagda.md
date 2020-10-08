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

  builtin- : ∀{o' o''}(b : Builtin)
    → Vec (ScopedTy 0) (arity⋆ b)
    → {tel : Tel Z o'}
    → VTel o' Z tel
    → Tel Z o''
    → arity b ≡ suc o' + o''
    → Frame

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

open import Data.Nat

VTel-extend : ∀{o}{tel : Tel Z o} → VTel o Z tel → {t : ScopedTm Z} → Value t → VTel (suc o) Z (tel :< t)
VTel-extend {tel = []}       vs         v = v ,, _
VTel-extend {tel = t' ∷ tel} (v' ,, vs) v = v' ,, VTel-extend vs v

vtel-lem : ∀{n n'}(p : n' ≡ n)(ts : Tel Z n') → VTel n' Z ts → VTel n Z (subst (Tel Z) p ts)
vtel-lem refl ts vs = vs

step : State → State
step (s ▻ Λ K L)    = s ◅ V-Λ {K = K} L
step (s ▻ (L ·⋆ A)) = (s , (-·⋆ A)) ▻ L
step (s ▻ ƛ A L)    = s ◅ V-ƛ A L
step (s ▻ (L · M))  = (s , (-· M)) ▻ L
step (s ▻ con cn)   = s ◅ V-con cn
  -- ^ why is i inferrable?

-- type telescope is full
step (s ▻ builtin bn (inj₁ (≤‴-refl ,, refl)) As ts) = s ▻ builtin bn (inj₂ (refl ,, z≤‴n)) As ts
-- type telescope is not full yet
step (s ▻ builtin bn (inj₁ (≤‴-step q ,, r)) As ts) = s ◅ V-builtin⋆ bn q As


-- term telescope is full
step (s ▻ builtin bn (inj₂ (q ,, ≤‴-refl)) As ts) with arity bn | inspect arity bn
-- (annoying special case for builtin with no args)
step (s ▻ builtin bn (inj₂ (refl ,, ≤‴-refl)) As ts)       | zero  | [[ eq ]] =
  s ▻ BUILTIN bn As (subst (Tel _) (sym eq) []) (vtel-lem (sym eq) [] tt)
-- (case for builtin with at least one arg)
step (s ▻ builtin bn (inj₂ (refl ,, ≤‴-refl)) As (t ∷ ts)) | suc n | [[ eq ]] =
  (s , builtin- bn As tt ts eq) ▻ t

-- term telescope is not full
step (s ▻ builtin bn (inj₂ (refl ,, ≤‴-step r)) As ts) = s ◅ V-builtin bn As r ts

step (s ▻ error A) = ◆
step (s ▻ wrap pat arg L) = (s , wrap- pat arg) ▻ L
step (s ▻ unwrap L) = (s , unwrap-) ▻ L
step (ε ◅ V) = □ V
step ((s , (-· M)) ◅ V) = (s , (V ·-)) ▻ M
step (_◅_ (s , (V-ƛ A L ·-)) {M} W) = s ▻ (L [ M ])
step ((s , (V-Λ V ·-)) ◅ W) = ◆
step ((s , (V-con tcn ·-)) ◅ W) = ◆
step ((s , (V-wrap A B V ·-)) ◅ W) = ◆
step ((s , (-·⋆ A)) ◅ V-ƛ A' L) = ◆
step ((s , (-·⋆ A)) ◅ V-Λ  t)  = s ▻ (t [ A ]⋆)
step ((s , (-·⋆ A)) ◅ V-con tcn) = ◆
step ((s , (-·⋆ A)) ◅ V-wrap A' B V) = ◆
step ((s , (-·⋆ A)) ◅ V-builtin b As q ts) = ◆
step ((s , wrap- A B) ◅ V) = s ◅ V-wrap A B V

-- β-unwrap
step ((s , unwrap-) ◅ V-wrap A B V) = s ◅ V
-- error conditions
step ((s , unwrap-) ◅ V-builtin b q As ts) = ◆
step ((s , unwrap-) ◅ V-builtin⋆ b q As) = ◆
step ((s , unwrap-) ◅ V-ƛ A t) = ◆
step ((s , unwrap-) ◅ V-Λ V) = ◆
step ((s , unwrap-) ◅ V-con tcn) = ◆
step ((s , (V-builtin⋆ b q As ·-)) ◅ V) = ◆

step (□ V) = □ V
step ◆     = ◆

-- some builtin related cases
-- processing of args done
step (_◅_ (s , builtin- b As {ts} vs [] q) {t} V) = s ▻ BUILTIN b As (subst (Tel _) (trans (+-comm 0 _) (sym q)) (ts :< t)) (vtel-lem (trans (+-comm 0 _) (sym q)) (ts :< t) (VTel-extend vs V))
-- more args to process
step (_◅_ (s , builtin- b As {ts} vs (t' ∷ ts') q) {t} V) =
  (s , builtin- b As { ts :< t } (VTel-extend vs V) ts' (trans q (cong suc (+-suc _ _)))) ▻ t'

step (_◅_ (s , (V-builtin b As q ts ·-)) {t} V) = s ▻ builtin b (inj₂ (refl ,, q)) As (ts :< t)
step ((s , (-·⋆ A)) ◅ V-builtin⋆ b q As) = s ▻ builtin b (inj₁ (q ,, refl)) (As :< A) []

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
