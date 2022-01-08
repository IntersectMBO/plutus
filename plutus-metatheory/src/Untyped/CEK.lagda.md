```
{-# OPTIONS --type-in-type #-}

module Untyped.CEK where
```

## Imports

```
open import Untyped
open import Untyped.RenamingSubstitution
open import Utils
open import Builtin
open import Algorithmic using (arity;Term;Type) -- TODO: move this stuff


open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false)
open import Data.Empty
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ;suc;zero)
open import Data.List using ([];_∷_)
```

```
data Value : Set
data Env : Set → Set where
  [] : Env ⊥
  _∷_ : ∀{X} → Env X → Value → Env (Maybe X)

data BApp (b : Builtin) : ∀{az}{as}
  → az <>> as ∈ arity b
  → Set

data Value where
  V-ƛ : ∀{X} → Env X → Maybe X ⊢ → Value
  V-con : TermCon → Value
  V-delay : ∀{X} → Env X → X ⊢ → Value
  V-I⇒ : ∀ b {as as'}
       → (p : as <>> (Term ∷ as') ∈ arity b)
       → BApp b p
       → Value
  V-IΠ : ∀ b  {as as'}
       → (p : as <>> (Type ∷ as') ∈ arity b)
       → BApp b p
       → Value

data BApp b where
  base : BApp b (start (arity b))
  app : ∀{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → BApp b p
    → Value
    → BApp b (bubble p)
  app⋆ : ∀{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → BApp b p
    → BApp b (bubble p)

env2sub : ∀{Γ} → Env Γ → Sub Γ ⊥

discharge : Value → ⊥ ⊢
dischargeB : ∀{b}{az}{as}{p : az <>> as ∈ arity b} → BApp b p → ⊥ ⊢

discharge (V-ƛ ρ t)     = ƛ (sub (lifts (env2sub ρ)) t)
discharge (V-con c)     = con c
discharge (V-delay ρ t) = delay (sub (env2sub ρ) t)
discharge (V-I⇒ b p vs) = dischargeB vs
discharge (V-IΠ b p vs) = dischargeB vs

dischargeB {b = b} base = builtin b
dischargeB (app p vs v) = dischargeB vs · discharge v
dischargeB (app⋆ p vs)   = force (dischargeB vs)

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


V-I : ∀ b {a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → BApp b p
       → Value
V-I b {a = Term} p vs = V-I⇒ b p vs
V-I b {a = Type} p vs = V-IΠ b p vs

BUILTIN : ∀ b → BApp b (saturated (arity b)) → Either RuntimeError Value
BUILTIN addInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i + i')))
BUILTIN subtractInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i - i')))
BUILTIN multiplyInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i ** i')))
BUILTIN divideInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ userError)
  (inj₂ (V-con (integer (div i i'))))
BUILTIN quotientInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ userError)
  (inj₂ (V-con (integer (quot i i'))))
BUILTIN remainderInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ userError)
  (inj₂ (V-con (integer (rem i i'))))
BUILTIN modInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ userError)
  (inj₂ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i <? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN lessThanEqualsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≤? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN equalsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≟ i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN appendByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bytestring (concat b b')))
BUILTIN lessThanByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B< b b')))
BUILTIN lessThanEqualsByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B> b b')))
BUILTIN sha2-256 (app _ base (V-con (bytestring b))) = inj₂ (V-con
  (bytestring (SHA2-256 b)))
BUILTIN sha3-256 (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (SHA3-256 b)))
BUILTIN blake2b-256 (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (BLAKE2B-256 b)))
BUILTIN verifySignature (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifySig k d c)
... | just b = inj₂ (V-con (bool b))
... | nothing = inj₁ userError
BUILTIN encodeUtf8 (app _ base (V-con (string s))) =
  inj₂ (V-con (bytestring (ENCODEUTF8 s)))
BUILTIN decodeUtf8 (app _ base (V-con (bytestring b))) with DECODEUTF8 b
... | nothing = inj₁ userError
... | just s  = inj₂ (V-con (string s))
BUILTIN equalsByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (equals b b')))
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base) (V-con (bool false))) vt) vf) = inj₂ vf
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base) (V-con (bool true))) vt) vf) = inj₂ vt
BUILTIN appendString (app _ (app _ base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (string (primStringAppend s s')))
BUILTIN trace (app _ (app _ (app⋆ _ base) (V-con (string s))) v) =
  inj₂ (TRACE s v)
BUILTIN iData (app _ base (V-con (integer i))) =
  inj₂ (V-con (Data (iDATA i)))
BUILTIN bData (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (Data (bDATA b)))
BUILTIN consByteString (app _ (app _ base (V-con (integer i))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (cons i b)))
BUILTIN sliceByteString (app _ (app _ (app _ base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (slice st n b)))
BUILTIN lengthOfByteString (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (integer (length b)))
BUILTIN indexByteString (app _ (app _ base (V-con (bytestring b))) (V-con (integer i))) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ userError
... | yes _ with i <? length b
... | no _  = inj₁ userError
... | yes _ = inj₂ (V-con (integer (index b i)))
BUILTIN equalsString (app _ (app _ base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (bool (primStringEquality s s')))
BUILTIN unIData (app _ base (V-con (Data (iDATA i)))) = inj₂ (V-con (integer i))
BUILTIN unBData (app _ base (V-con (Data (bDATA b)))) =
  inj₂ (V-con (bytestring b))
BUILTIN _ _ = inj₁ userError

convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b)
  → BApp b p
  → BApp b p'
convBApp b p p' q rewrite unique<>> p p' = q

BUILTIN' : ∀ b {az}(p : az <>> [] ∈ arity b)
  → BApp b p
  → ⊥ ⊢
BUILTIN' b {az = az} p q
  with sym (trans (cong ([] <><_) (sym (<>>2<>>' _ _ _ p))) (lemma<>2 az []))
... | refl with BUILTIN b (convBApp b p (saturated (arity b)) q)
... | inj₁ e = error
... | inj₂ V = discharge V

ival : Builtin → Value
ival addInteger = V-I⇒ addInteger _ base
ival subtractInteger = V-I⇒ subtractInteger _ base
ival multiplyInteger = V-I⇒ multiplyInteger _ base
ival divideInteger = V-I⇒ divideInteger _ base
ival quotientInteger = V-I⇒ quotientInteger _ base
ival remainderInteger = V-I⇒ remainderInteger _ base
ival modInteger = V-I⇒ modInteger _ base
ival lessThanInteger = V-I⇒ lessThanInteger _ base
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger _ base
ival equalsInteger = V-I⇒ equalsInteger _ base
ival appendByteString = V-I⇒ appendByteString _ base
ival lessThanByteString = V-I⇒ lessThanByteString _ base
ival lessThanEqualsByteString = V-I⇒ lessThanEqualsByteString _ base
ival sha2-256 = V-I⇒ sha2-256 _ base
ival sha3-256 = V-I⇒ sha3-256 _ base
ival verifySignature = V-I⇒ verifySignature _ base
ival equalsByteString = V-I⇒ equalsByteString _ base
ival ifThenElse = V-IΠ ifThenElse _ base
ival appendString = V-I⇒ appendString _ base
ival trace = V-IΠ trace _ base
ival equalsString = V-I⇒ equalsString (start _) base
ival encodeUtf8 = V-I⇒ encodeUtf8 (start _) base
ival decodeUtf8 = V-I⇒ decodeUtf8 (start _) base
ival fstPair = V-IΠ fstPair (start _) base
ival sndPair = V-IΠ sndPair (start _) base
ival nullList = V-IΠ nullList (start _) base
ival headList = V-IΠ headList (start _) base
ival tailList = V-IΠ tailList (start _) base
ival chooseList = V-IΠ chooseList (start _) base
ival constrData = V-I⇒ constrData (start _) base
ival mapData = V-I⇒ mapData (start _) base
ival listData = V-I⇒ listData (start _) base
ival iData = V-I⇒ iData (start _) base
ival bData = V-I⇒ bData (start _) base
ival unConstrData = V-I⇒ unConstrData (start _) base
ival unMapData = V-I⇒ unMapData (start _) base
ival unListData = V-I⇒ unListData (start _) base
ival unIData = V-I⇒ unIData (start _) base
ival unBData = V-I⇒ unBData (start _) base
ival equalsData = V-I⇒ equalsData (start _) base
ival chooseData = V-IΠ chooseData (start _) base
ival chooseUnit = V-IΠ chooseUnit (start _) base
ival mkPairData = V-I⇒ mkPairData (start _) base
ival mkNilData = V-I⇒ mkNilData (start _) base
ival mkNilPairData = V-I⇒ mkNilPairData (start _) base
ival mkCons = V-I⇒ mkCons (start _) base
ival consByteString = V-I⇒ consByteString (start _) base
ival sliceByteString = V-I⇒ sliceByteString (start _) base
ival lengthOfByteString = V-I⇒ lengthOfByteString (start _) base
ival indexByteString = V-I⇒ indexByteString (start _) base
ival blake2b-256 = V-I⇒ blake2b-256 (start _) base

step : State → State
step (s ; ρ ▻ ` x)       = s ◅ lookup ρ x
step (s ; ρ ▻ ƛ t)       = s ◅ V-ƛ ρ t
step (s ; ρ ▻ (t · u))   = (s , -· ρ u) ; ρ ▻ t
step (s ; ρ ▻ force t)   = (s , force-) ; ρ ▻ t
step (s ; ρ ▻ delay t)   = s ◅ V-delay ρ t
step (s ; ρ ▻ con c)     = s ◅ V-con c
step (s ; ρ ▻ builtin b) = s ◅ ival b
step (s ; ρ ▻ error)     = ◆
step (ε ◅ v)             = □ v
step ((s , -· ρ u) ◅ v)  = (s , (v ·-)) ; ρ ▻ u
step ((s , (V-ƛ ρ t ·-)) ◅ v) = s ; ρ ∷ v ▻ t
step ((s , (V-I⇒ b {as' = []} p vs ·-)) ◅ v) =
  s ; [] ▻ BUILTIN' b (bubble p) (app p vs v)
step ((s , (V-I⇒ b {as' = a ∷ as'} p vs ·-)) ◅ v) =
  s ◅ V-I b (bubble p) (app p vs v)
step ((s , (V-con _     ·-)) ◅ v) = ◆ -- constant in function position
step ((s , (V-delay _ _ ·-)) ◅ v) = ◆ -- delay in function position
step ((s , (V-IΠ b p vs ·-)) ◅ v) = ◆ -- delayed builtin in function position
step ((s , force-) ◅ V-IΠ b {as' = []} p vs) =
  s ; [] ▻ BUILTIN' b (bubble p) (app⋆ p vs)
step ((s , force-) ◅ V-IΠ b {as' = a ∷ as'} p vs) =
  s ◅ V-I b (bubble p) (app⋆ p vs)
step ((s , force-) ◅ V-delay ρ t) = step (s ; ρ ▻ t)
step ((s , force-) ◅ V-ƛ _ _)     = ◆ -- lambda in delay position
step ((s , force-) ◅ V-con _)     = ◆ -- constant in delay position
step ((s , force-) ◅ V-I⇒ b p vs) = ◆ -- function in delay position

step (□ v)               = □ v
step ◆                   = ◆

open import Function
stepper : ℕ → (t : State) → Either RuntimeError State
stepper 0       s = inj₁ gasError
stepper (suc n) s with step s
... | (s ; ρ ▻ t) = stepper n (s ; ρ ▻ t)
... | (s ◅ v)     = stepper n (s ◅ v)
... | (□ v)       = return (□ v)
... | ◆           = return ◆
