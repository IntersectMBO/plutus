```
{-# OPTIONS --type-in-type #-}

module Untyped.CEK where
```

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
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
open import Builtin.Signature using (Sig;sig;Args;_⊢♯;nat2Ctx⋆;fin2∈⋆;args♯)
open Sig
```

```
data Value : Set
data Env : Set → Set where
  [] : Env ⊥
  _∷_ : ∀{X} → Env X → Value → Env (Maybe X)

data BApp (b : Builtin) :
    ∀{tn tm tt} → (pt : tn ∔ tm ≣ tt)
  → ∀{an am at} → (pa : an ∔ am ≣ at)
  → Set

data Value where
  V-ƛ : ∀{X} → Env X → Maybe X ⊢ → Value
  V-con : TermCon → Value
  V-delay : ∀{X} → Env X → X ⊢ → Value
  V-I⇒ : ∀ b {tn} 
       → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → BApp b pt pa
       → Value
  V-IΠ : ∀ b 
       → ∀{tn tm}{pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → BApp b pt pa
       → Value

data BApp b where
  base : BApp b (start (fv♯ (signature b))) (start (args♯ (signature b)))
  app : ∀{tn}
      {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → BApp b pt pa
    → Value
    → BApp b pt (bubble pa)
  app⋆ : 
      ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → BApp b pt pa
    → BApp b (bubble pt) pa

env2sub : ∀{Γ} → Env Γ → Sub Γ ⊥

discharge : Value → ⊥ ⊢

dischargeB : ∀{b}
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv♯ (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → BApp b pt pa → ⊥ ⊢

discharge (V-ƛ ρ t)     = ƛ (sub (lifts (env2sub ρ)) t)
discharge (V-con c)     = con c
discharge (V-delay ρ t) = delay (sub (env2sub ρ) t)
discharge (V-I⇒ b vs) = dischargeB vs
discharge (V-IΠ b vs) = dischargeB vs

dischargeB {b = b} base = builtin b
dischargeB (app vs v) = dischargeB vs · discharge v
dischargeB (app⋆ vs)   = force (dischargeB vs)

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

V-I : ∀ b 
    → ∀{tn tm} {pt : tn ∔ tm ≣ fv♯ (signature b)}
    → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
    → BApp b pt pa
    → Value
V-I b {tm = zero}   bt = V-I⇒ b bt
V-I b {tm = suc tm} bt = V-IΠ b bt

BUILTIN : ∀ b → BApp b (alldone (fv♯ (signature b))) (alldone (args♯ (signature b))) → Either RuntimeError Value
BUILTIN addInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i + i')))  
  ; _ -> inj₁ userError
  }
BUILTIN subtractInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i - i')))
  ; _ -> inj₁ userError
  }
BUILTIN multiplyInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> inj₂ (V-con (integer (i ** i')))
  ; _ -> inj₁ userError
  }
BUILTIN divideInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (div i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN quotientInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (quot i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN remainderInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (rem i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN modInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con (integer (mod i i'))))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf (i <? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf (i ≤? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN equalsInteger = λ
  { (app (app base (V-con (integer i))) (V-con (integer i'))) -> decIf (i ≟ i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
  ; _ -> inj₁ userError
  }
BUILTIN appendByteString = λ
  { (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bytestring (concat b b')))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanByteString = λ
  { (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (B< b b')))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsByteString = λ
  { (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (B<= b b')))
  ; _ -> inj₁ userError
  }
BUILTIN sha2-256 = λ
  { (app base (V-con (bytestring b))) -> inj₂ (V-con
      (bytestring (SHA2-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN sha3-256 = λ
  { (app base (V-con (bytestring b))) ->
      inj₂ (V-con (bytestring (SHA3-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN blake2b-256 = λ
  { (app base (V-con (bytestring b))) ->
      inj₂ (V-con (bytestring (BLAKE2B-256 b)))
  ; _ -> inj₁ userError
  }
BUILTIN verifyEd25519Signature = λ
  { (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifyEd25519Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifyEcdsaSecp256k1Signature = λ
  { (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifyEcdsaSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifySchnorrSecp256k1Signature = λ
  { (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) -> case verifySchnorrSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con (bool b))
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN encodeUtf8 = λ
  { (app base (V-con (string s))) ->
      inj₂ (V-con (bytestring (ENCODEUTF8 s)))
  ; _ -> inj₁ userError
  }
BUILTIN decodeUtf8 = λ
  { (app base (V-con (bytestring b))) ->
      case DECODEUTF8 b of λ
        { (just s) -> inj₂ (V-con (string s))
        ; nothing -> inj₁ userError
        }
  ; _ -> inj₁ userError
  }
BUILTIN equalsByteString = λ
  { (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) -> inj₂ (V-con (bool (equals b b')))
  ; _ -> inj₁ userError
  }
BUILTIN ifThenElse = λ
  { (app (app (app (app⋆ base) (V-con (bool b))) vt) vf) -> inj₂ $ if b then vt else vf
  ; _ -> inj₁ userError
  }
BUILTIN appendString = λ
  { (app (app base (V-con (string s))) (V-con (string s'))) -> inj₂ (V-con (string (primStringAppend s s')))
  ; _ -> inj₁ userError
  }
BUILTIN trace = λ
  { (app (app (app⋆ base) (V-con (string s))) v) -> inj₂ (TRACE s v)
  ; _ -> inj₁ userError
  }
BUILTIN iData = λ
  { (app base (V-con (integer i))) -> inj₂ (V-con (pdata (iDATA i)))
  ; _ -> inj₁ userError
  }
BUILTIN bData = λ
  { (app base (V-con (bytestring b))) -> inj₂ (V-con (pdata (bDATA b)))
  ; _ -> inj₁ userError
  }
BUILTIN consByteString = λ
  { (app (app base (V-con (integer i))) (V-con (bytestring b))) -> inj₂ (V-con (bytestring (cons i b)))
  ; _ -> inj₁ userError
  }
BUILTIN sliceByteString = λ
  { (app (app (app base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) -> inj₂ (V-con (bytestring (slice st n b)))
  ; _ -> inj₁ userError
  }
BUILTIN lengthOfByteString = λ
  { (app base (V-con (bytestring b))) -> inj₂ (V-con (integer (length b)))
  ; _ -> inj₁ userError
  }
BUILTIN indexByteString = λ
  { (app (app base (V-con (bytestring b))) (V-con (integer i))) ->
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
  { (app (app base (V-con (string s))) (V-con (string s'))) -> inj₂ (V-con (bool (primStringEquality s s')))
  ; _ -> inj₁ userError
  }
BUILTIN unIData = λ
  { (app base (V-con (pdata (iDATA i)))) -> inj₂ (V-con (integer i))
  ; _ -> inj₁ userError
  }
BUILTIN unBData = λ
  { (app base (V-con (pdata (bDATA b)))) -> inj₂ (V-con (bytestring b))
  ; _ -> inj₁ userError
  }
BUILTIN serialiseData = λ
  { (app base (V-con (pdata d))) -> inj₂ (V-con (bytestring (serialiseDATA d)))
  ; _ -> inj₁ userError
  }
BUILTIN chooseUnit = λ
  { (app (app (app⋆ base) (V-con unit)) v) -> inj₂ v
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

BUILTIN' : ∀ b
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv♯ (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → BApp b pt pa
  → ⊥ ⊢
BUILTIN' b {pt = pt} {pa = pa} bt with trans (sym (+-identityʳ _)) (∔2+ pt) | trans (sym (+-identityʳ _)) (∔2+ pa)
... | refl | refl with unique∔ pt (alldone (fv♯ (signature b))) | unique∔ pa (alldone (args♯ (signature b)))
... | refl | refl with BUILTIN b bt
... | inj₁ _ = error
... | inj₂ V = discharge V

ival : Builtin → Value
ival b = V-I b base

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
step ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ v) =
  s ; [] ▻ BUILTIN' b (app bapp v)
step ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ v) =
  s ◅ V-I b (app bapp v)
step ((s , (V-con _     ·-)) ◅ v) = ◆ -- constant in function position
step ((s , (V-delay _ _ ·-)) ◅ v) = ◆ -- delay in function position
step ((s , (V-IΠ b bapp ·-)) ◅ v) = ◆ -- delayed builtin in function position
step ((s , force-) ◅ V-IΠ b bapp) = s ◅ V-I b (app⋆ bapp)
step ((s , force-) ◅ V-delay ρ t) = step (s ; ρ ▻ t)
step ((s , force-) ◅ V-ƛ _ _)     = ◆ -- lambda in delay position
step ((s , force-) ◅ V-con _)     = ◆ -- constant in delay position
step ((s , force-) ◅ V-I⇒ b bapp) = ◆ -- function in delay position

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
