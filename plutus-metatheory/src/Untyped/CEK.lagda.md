```
{-# OPTIONS --type-in-type #-}

module Untyped.CEK where
```

## Imports

```
open import Function using (case_of_;_$_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false;if_then_else_)
open import Data.Empty using (⊥)
open import Agda.Builtin.String using (primStringAppend; primStringEquality)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (refl;sym;trans;cong)
open import Data.Nat using (ℕ;suc)
open import Data.List using ([];_∷_)

open import Untyped using (_⊢)
open _⊢
open import Untyped.RenamingSubstitution using (Sub;sub;lifts)
open import Utils 
open import Builtin
open import Algorithmic using (arity;Term;Type)
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
BUILTIN addInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i + i')))  ; _ -> inj₁ userError
  }
BUILTIN subtractInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i - i')))
  ; _ -> inj₁ userError
  }
BUILTIN multiplyInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i ** i')))
  ; _ -> inj₁ userError
  }
BUILTIN divideInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (div i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN quotientInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (quot i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN remainderInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (rem i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN modInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (mod i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf (i <? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf (i ≤? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN equalsInteger = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) -> decIf (i ≟ i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN appendByteString = λ
  { (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bytestring (concat b b')))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanByteString = λ
  { (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (B< b b')))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsByteString = λ
  { (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (B<= b b')))
  ; _ -> inj₁ userError
  }
BUILTIN sha2-256 = λ
  { (app _ base (V-con (bytestring b))) -> inj₂ (V-con
      (bytestring (SHA2-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN sha3-256 = λ
  { (app _ base (V-con (bytestring b))) ->
      inj₂ (V-con (bytestring (SHA3-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN blake2b-256 = λ
  { (app _ base (V-con (bytestring b))) ->
      inj₂ (V-con (bytestring (BLAKE2B-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN verifyEd25519Signature = λ
  { (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifyEd25519Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifyEcdsaSecp256k1Signature = λ
  { (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifyEcdsaSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifySchnorrSecp256k1Signature = λ
  { (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifySchnorrSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN encodeUtf8 = λ
  { (app _ base (V-con (string s))) ->
      inj₂ (V-con (bytestring (ENCODEUTF8 s)))
  ; _ -> inj₁ userError
  }
BUILTIN decodeUtf8 = λ
  { (app _ base (V-con (bytestring b))) ->
      case DECODEUTF8 b of λ
        { (just s) -> inj₂ (V-con (string s))
        ; nothing -> inj₁ userError
        }
  ; _ -> inj₁ userError
  }
BUILTIN equalsByteString = λ
  { (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (equals b b')))
  ; _ -> inj₁ userError
  }
BUILTIN ifThenElse = λ
  { (app _ (app _ (app _ (app⋆ _ base) (V-con (bool b))) vt) vf) -> inj₂ $ if b then vt else vf
  ; _ -> inj₁ userError
  }
BUILTIN appendString = λ
  { (app _ (app _ base (V-con (string s))) (V-con (string s'))) -> inj₂ (V-con (string (primStringAppend s s')))
  ; _ -> inj₁ userError
  }
BUILTIN trace = λ
  { (app _ (app _ (app⋆ _ base) (V-con (string s))) v) -> inj₂ (TRACE s v)
  ; _ -> inj₁ userError
  }
BUILTIN iData = λ
  { (app _ base (V-con (integer i))) -> inj₂ (V-con (pdata (iDATA i)))
  ; _ -> inj₁ userError
  }
BUILTIN bData = λ
  { (app _ base (V-con (bytestring b))) -> inj₂ (V-con (pdata (bDATA b)))
  ; _ -> inj₁ userError
  }
BUILTIN consByteString = λ
  { (app _ (app _ base (V-con (integer i))) (V-con (bytestring b))) -> inj₂ (V-con (bytestring (cons i b)))
  ; _ -> inj₁ userError
  }
BUILTIN sliceByteString = λ
  { (app _ (app _ (app _ base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) -> inj₂ (V-con (bytestring (slice st n b)))
  ; _ -> inj₁ userError
  }
BUILTIN lengthOfByteString = λ
  { (app _ base (V-con (bytestring b))) -> inj₂ (V-con (integer (length b)))
  ; _ -> inj₁ userError
  }
BUILTIN indexByteString = λ
  { (app _ (app _ base (V-con (bytestring b))) (V-con (integer i))) ->
      case Data.Integer.ℤ.pos 0 ≤? i of λ
        { (no  _) -> inj₁ userError
        ; (yes _) -> case i <? length b of λ
          { (no _)  -> inj₁ userError
          ; (yes _) -> inj₂ (V-con (integer (index b i)))
          }
        }
  ; _ -> inj₁ userError
  }
BUILTIN equalsString = λ
  { (app _ (app _ base (V-con (string s))) (V-con (string s'))) -> inj₂ (V-con (bool (primStringEquality s s')))
  ; _ -> inj₁ userError
  }
BUILTIN unIData = λ
  { (app _ base (V-con (pdata (iDATA i)))) -> inj₂ (V-con (integer i))
  ; _ -> inj₁ userError
  }
BUILTIN unBData = λ
  { (app _ base (V-con (pdata (bDATA b)))) -> inj₂ (V-con (bytestring b))
  ; _ -> inj₁ userError
  }
BUILTIN serialiseData = λ
  { (app _ base (V-con (pdata d))) -> inj₂ (V-con (bytestring (serialiseDATA d)))
  ; _ -> inj₁ userError
  }
BUILTIN chooseUnit = λ
  { (app _ (app _ (app⋆ _ base) (V-con unit)) v) -> inj₂ v
  ; _ -> inj₁ userError
  }
BUILTIN fstPair = λ
  { _ -> inj₁ userError
  }
BUILTIN sndPair = λ
  { _ -> inj₁ userError
  }
BUILTIN chooseList = λ
  { _ -> inj₁ userError
  }
BUILTIN mkCons = λ
  { _ -> inj₁ userError
  }
BUILTIN headList = λ
  { _ -> inj₁ userError
  }
BUILTIN tailList = λ
  { _ -> inj₁ userError
  }
BUILTIN nullList = λ
  { _ -> inj₁ userError
  }
BUILTIN chooseData = λ
  { _ -> inj₁ userError
  }
BUILTIN constrData = λ
  { _ -> inj₁ userError
  }
BUILTIN mapData = λ
  { _ -> inj₁ userError
  }
BUILTIN listData = λ
  { _ -> inj₁ userError
  }
BUILTIN unConstrData = λ
  { _ -> inj₁ userError
  }
BUILTIN unMapData = λ
  { _ -> inj₁ userError
  }
BUILTIN unListData = λ
  { _ -> inj₁ userError
  }
BUILTIN equalsData = λ
  { _ -> inj₁ userError
  }
BUILTIN mkPairData = λ
  { _ -> inj₁ userError
  }
BUILTIN mkNilData = λ
  { _ -> inj₁ userError
  }
BUILTIN mkNilPairData = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-add = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-neg = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-scalarMul = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-equal = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-hashToCurve = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-compress = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-uncompress = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-add = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-neg = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-scalarMul = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-equal = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-hashToCurve = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-compress = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-uncompress = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-pairing = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-mulMlResult = λ
  { _ -> inj₁ userError
  }
BUILTIN bls12-381-finalVerify = λ
  { _ -> inj₁ userError
  }

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
ival verifyEd25519Signature = V-I⇒ verifyEd25519Signature _ base
ival verifyEcdsaSecp256k1Signature = V-I⇒ verifyEcdsaSecp256k1Signature _ base
ival verifySchnorrSecp256k1Signature = V-I⇒ verifySchnorrSecp256k1Signature _ base
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
ival serialiseData = V-I⇒ serialiseData (start _) base
ival chooseData = V-IΠ chooseData (start _) base
ival chooseUnit = V-IΠ chooseUnit (start _) base
ival mkPairData = V-I⇒ mkPairData (start _) base
ival mkNilData = V-I⇒ mkNilData (start _) base
ival mkNilPairData = V-I⇒ mkNilPairData (start _) base
ival mkCons = V-IΠ mkCons (start _) base
ival consByteString = V-I⇒ consByteString (start _) base
ival sliceByteString = V-I⇒ sliceByteString (start _) base
ival lengthOfByteString = V-I⇒ lengthOfByteString (start _) base
ival indexByteString = V-I⇒ indexByteString (start _) base
ival blake2b-256 = V-I⇒ blake2b-256 (start _) base
ival bls12-381-G1-add = V-I⇒ bls12-381-G1-add (start _) base
ival bls12-381-G1-neg = V-I⇒ bls12-381-G1-neg (start _) base
ival bls12-381-G1-scalarMul = V-I⇒ bls12-381-G1-scalarMul (start _) base
ival bls12-381-G1-equal = V-I⇒ bls12-381-G1-equal (start _) base
ival bls12-381-G1-hashToCurve = V-I⇒ bls12-381-G1-hashToCurve (start _) base
ival bls12-381-G1-compress = V-I⇒ bls12-381-G1-compress (start _) base
ival bls12-381-G1-uncompress = V-I⇒ bls12-381-G1-uncompress (start _) base
ival bls12-381-G2-add = V-I⇒ bls12-381-G2-add (start _) base
ival bls12-381-G2-neg = V-I⇒ bls12-381-G2-neg (start _) base
ival bls12-381-G2-scalarMul = V-I⇒ bls12-381-G2-scalarMul (start _) base
ival bls12-381-G2-equal = V-I⇒ bls12-381-G2-equal (start _) base
ival bls12-381-G2-hashToCurve = V-I⇒ bls12-381-G2-hashToCurve (start _) base
ival bls12-381-G2-compress = V-I⇒ bls12-381-G2-compress (start _) base
ival bls12-381-G2-uncompress = V-I⇒ bls12-381-G2-uncompress (start _) base
ival bls12-381-pairing = V-I⇒ bls12-381-pairing (start _) base
ival bls12-381-mulMlResult = V-I⇒ bls12-381-mulMlResult (start _) base
ival bls12-381-finalVerify = V-I⇒ bls12-381-finalVerify (start _) base


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
