---
title: Untyped.CEK
layout: page
---
```
{-# OPTIONS --type-in-type #-}

module Untyped.CEK where
```

## Imports

```
open import Data.Unit using (tt)
open import Data.Fin using (Fin;suc;zero)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Function using (case_of_;_$_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false;if_then_else_)
open import Data.Empty using (⊥)
open import Agda.Builtin.String using (primStringAppend; primStringEquality)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (refl;sym;trans;cong)
open import Data.List using (List;[];_∷_)
open import Data.Product using (_,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Untyped using (_⊢)
open _⊢
open import Untyped.RenamingSubstitution using (Sub;sub;lifts)
open import Utils hiding (List;length)
open import Builtin
open import Builtin.Signature using (Sig;sig;Args;_⊢♯;args♯;fv)
            using (integer;bool;bytestring;string;pdata;unit;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult)
open _⊢♯
open Sig
open import RawU using (TmCon;tmCon;TyTag;decTyTag;⟦_⟧tag)
```

```
data Stack (A : Set) : Set where
  ε : Stack A
  _,_ : Stack A → A → Stack A
```

```
data Value : Set
data Env : ℕ → Set where
  [] : Env 0
  _∷_ : ∀{X} → Env X → Value → Env (suc X)

data BApp (b : Builtin) :
    ∀{tn tm tt} → (pt : tn ∔ tm ≣ tt)
  → ∀{an am at} → (pa : an ∔ am ≣ at)
  → Set

data Value where
  V-ƛ : ∀{X} → Env X → suc X ⊢ → Value
  V-con : (ty : TyTag) → ⟦ ty ⟧tag → Value
  V-delay : ∀{X} → Env X → X ⊢ → Value
  V-constr : (i : ℕ) → (vs : Stack Value) → Value
  V-I⇒ : ∀ b {tn}
       → {pt : tn ∔ 0 ≣ fv (signature b)}
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → BApp b pt pa
       → Value
  V-IΠ : ∀ b
       → ∀{tn tm}{pt : tn ∔ (suc tm) ≣ fv (signature b)}
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → BApp b pt pa
       → Value

data BApp b where
  base : BApp b (start (fv (signature b))) (start (args♯ (signature b)))
  app : ∀{tn}
      {pt : tn ∔ 0 ≣ fv (signature b)}
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → BApp b pt pa
    → Value
    → BApp b pt (bubble pa)
  app⋆ :
      ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv (signature b)}
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → BApp b pt pa
    → BApp b (bubble pt) pa

env2sub : ∀{Γ} → Env Γ → Sub Γ 0

discharge : Value → 0 ⊢

dischargeB : ∀{b}
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → BApp b pt pa → 0 ⊢

dischargeList : Stack Value → List (0 ⊢) → List (0 ⊢)

discharge (V-ƛ ρ t)       = ƛ (sub (lifts (env2sub ρ)) t)
discharge (V-con t c)     = con (tmCon t c)
discharge (V-delay ρ t)   = delay (sub (env2sub ρ) t)
discharge (V-I⇒ b vs)     = dischargeB vs
discharge (V-IΠ b vs)     = dischargeB vs
discharge (V-constr i vs) = constr i (dischargeList vs [])

dischargeList ε ts = ts
dischargeList (xs , x) ts = dischargeList xs (discharge x ∷ ts)

dischargeB {b = b} base = builtin b
dischargeB (app vs v) = dischargeB vs · discharge v
dischargeB (app⋆ vs)   = force (dischargeB vs)

env2sub (ρ ∷ v) zero  = discharge v
env2sub (ρ ∷ v) (suc x) = env2sub ρ x

data Frame : Set where
  -·  : ∀{Γ} → Env Γ → Γ ⊢ → Frame
  -·v : Value → Frame
  _·- : Value → Frame
  force- : Frame
  constr- : ∀{Γ} → ℕ → (Stack Value) → Env Γ → List (Γ ⊢) → Frame
  case- : ∀{Γ} → (ρ : Env Γ) → List (Γ ⊢) → Frame


data State : Set where
  _;_▻_ : {X : ℕ} → Stack Frame → Env X → X ⊢ → State
  _◅_   : Stack Frame → Value → State
  □ : Value → State
  ◆ : State

-- lookup is the same as env2sub without the discharge
lookup : ∀{Γ} → Env Γ → Fin Γ → Value
lookup (ρ ∷ v) zero  = v
lookup (ρ ∷ v) (suc x) = lookup ρ x

V-I : ∀ b
    → ∀{tn tm} {pt : tn ∔ tm ≣ fv (signature b)}
    → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
    → BApp b pt pa
    → Value
V-I b {tm = zero}   bt = V-I⇒ b bt
V-I b {tm = suc tm} bt = V-IΠ b bt

fullyAppliedBuiltin : ∀ b → Set
fullyAppliedBuiltin b = BApp b (alldone (fv (signature b))) (alldone (args♯ (signature b)))

{-
The BUILTIN function provides the semantics of builtin functions.
-}

BUILTIN : ∀ b → fullyAppliedBuiltin b → Either RuntimeError Value
BUILTIN addInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> inj₂ (V-con integer (i + i'))
  ; _ -> inj₁ userError
  }
BUILTIN subtractInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> inj₂ (V-con integer (i - i'))
  ; _ -> inj₁ userError
  }
BUILTIN multiplyInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> inj₂ (V-con integer (i ** i'))
  ; _ -> inj₁ userError
  }
BUILTIN divideInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con integer (div i i')))
  ; _ -> inj₁ userError
  }
BUILTIN quotientInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con integer (quot i i')))
  ; _ -> inj₁ userError
  }
BUILTIN remainderInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con integer (rem i i')))
  ; _ -> inj₁ userError
  }
BUILTIN modInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf
      (i' ≟ ℤ.pos 0)
      (inj₁ userError)
      (inj₂ (V-con integer (mod i i')))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf (i <? i') (inj₂ (V-con bool true)) (inj₂ (V-con bool false))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf (i ≤? i') (inj₂ (V-con bool true)) (inj₂ (V-con bool false))
  ; _ -> inj₁ userError
  }
BUILTIN equalsInteger = λ
  { (app (app base (V-con integer i)) (V-con integer i')) -> decIf (i ≟ i') (inj₂ (V-con bool true)) (inj₂ (V-con bool false))
  ; _ -> inj₁ userError
  }
BUILTIN appendByteString = λ
  { (app (app base (V-con bytestring b)) (V-con bytestring b')) -> inj₂ (V-con bytestring (concat b b'))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanByteString = λ
  { (app (app base (V-con bytestring b)) (V-con bytestring b')) -> inj₂ (V-con bool (B< b b'))
  ; _ -> inj₁ userError
  }
BUILTIN lessThanEqualsByteString = λ
  { (app (app base (V-con bytestring b)) (V-con bytestring b')) -> inj₂ (V-con bool (B<= b b'))
  ; _ -> inj₁ userError
  }
BUILTIN sha2-256 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (SHA2-256 b))
  ; _ -> inj₁ userError
  }
BUILTIN sha3-256 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (SHA3-256 b))
  ; _ -> inj₁ userError
  }
BUILTIN blake2b-256 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (BLAKE2B-256 b))
  ; _ -> inj₁ userError
  }
BUILTIN verifyEd25519Signature = λ
  { (app (app (app base (V-con bytestring k)) (V-con bytestring d)) (V-con bytestring c)) -> case verifyEd25519Sig k d c of λ
      { (just b) -> inj₂ (V-con bool b)
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifyEcdsaSecp256k1Signature = λ
  { (app (app (app base (V-con bytestring k)) (V-con bytestring d)) (V-con bytestring c)) -> case verifyEcdsaSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con bool b)
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN verifySchnorrSecp256k1Signature = λ
  { (app (app (app base (V-con bytestring k)) (V-con bytestring d)) (V-con bytestring c)) -> case verifySchnorrSecp256k1Sig k d c of λ
      { (just b) -> inj₂ (V-con bool b)
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN encodeUtf8 = λ
  { (app base (V-con string s)) ->
      inj₂ (V-con bytestring (ENCODEUTF8 s))
  ; _ -> inj₁ userError
  }
BUILTIN decodeUtf8 = λ
  { (app base (V-con bytestring b)) ->
      case DECODEUTF8 b of λ
        { (just s) -> inj₂ (V-con string s)
        ; nothing -> inj₁ userError
        }
  ; _ -> inj₁ userError
  }
BUILTIN equalsByteString = λ
  { (app (app base (V-con bytestring b)) (V-con bytestring b')) -> inj₂ (V-con bool (equals b b'))
  ; _ -> inj₁ userError
  }
BUILTIN ifThenElse = λ
  { (app (app (app (app⋆ base) (V-con bool b)) vt) vf) -> inj₂ $ if b then vt else vf
  ; _ -> inj₁ userError
  }
BUILTIN appendString = λ
  { (app (app base (V-con string s)) (V-con string s')) -> inj₂ (V-con string (primStringAppend s s'))
  ; _ -> inj₁ userError
  }
BUILTIN trace = λ
  { (app (app (app⋆ base) (V-con string s)) v) -> inj₂ (TRACE s v)
  ; _ -> inj₁ userError
  }
BUILTIN iData = λ
  { (app base (V-con integer i)) -> inj₂ (V-con pdata (iDATA i))
  ; _ -> inj₁ userError
  }
BUILTIN bData = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con pdata (bDATA b))
  ; _ -> inj₁ userError
  }
BUILTIN consByteString (app (app base (V-con integer i)) (V-con bytestring b))  with cons i b
... | just b' = inj₂ (V-con bytestring b')
... | nothing = inj₁ userError
BUILTIN consByteString _ = inj₁ userError
BUILTIN sliceByteString = λ
  { (app (app (app base (V-con integer st)) (V-con integer n)) (V-con bytestring b)) -> inj₂ (V-con bytestring (slice st n b))
  ; _ -> inj₁ userError
  }
BUILTIN lengthOfByteString = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con integer (lengthBS b))
  ; _ -> inj₁ userError
  }
BUILTIN indexByteString = λ
  { (app (app base (V-con bytestring b)) (V-con integer i)) ->
      case Data.Integer.ℤ.pos 0 ≤? i of λ
        { (no  _) -> inj₁ userError
        ; (yes _) -> case i <? lengthBS b of λ
          { (no _)  -> inj₁ userError
          ; (yes _) -> inj₂ (V-con integer (index b i))
          }
        }
  ; _ -> inj₁ userError
  }
BUILTIN equalsString = λ
  { (app (app base (V-con string s)) (V-con string s')) -> inj₂ (V-con bool (primStringEquality s s'))
  ; _ -> inj₁ userError
  }
BUILTIN unIData = λ
  { (app base (V-con pdata (iDATA i))) -> inj₂ (V-con integer i)
  ; _ -> inj₁ userError
  }
BUILTIN unBData = λ
  { (app base (V-con pdata (bDATA b))) -> inj₂ (V-con bytestring b)
  ; _ -> inj₁ userError
  }
BUILTIN serialiseData = λ
  { (app base (V-con pdata d)) -> inj₂ (V-con bytestring (serialiseDATA d))
  ; _ -> inj₁ userError
  }
BUILTIN chooseUnit = λ
  { (app (app (app⋆ base) (V-con unit tt)) v) -> inj₂ v
  ; _ -> inj₁ userError
  }
BUILTIN fstPair = λ
  { (app (app⋆ (app⋆ base)) (V-con (pair t _) (x , _))) -> inj₂ (V-con t x)
  ; _ -> inj₁ userError
  }
BUILTIN sndPair = λ
  { (app (app⋆ (app⋆ base)) (V-con (pair _ t) (_ , y))) → inj₂ (V-con t y)
  ; _ -> inj₁ userError
  }
BUILTIN chooseList = λ
  { (app (app (app (app⋆ (app⋆ base)) (V-con (list _) [])) v) _) → inj₂ v
  ; (app (app (app (app⋆ (app⋆ base)) (V-con (list _) (_ ∷ _))) _) v) → inj₂ v
  ; _ -> inj₁ userError
  }
BUILTIN mkCons (app (app (app⋆ base) (V-con t x)) (V-con (list ts) xs)) with decTyTag t ts
... | yes refl = inj₂ (V-con (list ts) (x ∷ xs))
... | no _     = inj₁ userError
BUILTIN mkCons _ = inj₁ userError
BUILTIN headList = λ
  { (app (app⋆ base) (V-con (list t) (x ∷ _))) → inj₂ (V-con t x)
  ; _ -> inj₁ userError
  }
BUILTIN tailList = λ
  { (app (app⋆ base) (V-con (list t) (_ ∷ xs))) → inj₂ (V-con (list t) xs)
  ; _ -> inj₁ userError
  }
BUILTIN nullList = λ
  { (app (app⋆ base) (V-con (list _) [])) → inj₂ (V-con bool true)
  ; (app (app⋆ base) (V-con (list _) (_ ∷ _))) → inj₂ (V-con bool false)
  ; _ -> inj₁ userError
  }
BUILTIN lengthOfArray = λ
  { (app (app⋆ base) (V-con (array _) as)) → inj₂ (V-con integer (Utils.HSlengthOfArray as))
    ; _ -> inj₁ userError
  }
BUILTIN listToArray = λ
  { (app (app⋆ base) (V-con (list t) ls)) → inj₂ (V-con (array t) (Utils.HSlistToArray ls))
    ; _ -> inj₁ userError
  }
BUILTIN indexArray = λ
  { (app (app (app⋆ base) (V-con (array t) as)) (V-con integer i)) →
      case Data.Integer.ℤ.pos 0 ≤? i of λ
        { (no  _) -> inj₁ userError
        ; (yes _) -> case i <? Utils.HSlengthOfArray as of λ
          { (no _)  -> inj₁ userError
          ; (yes _) -> inj₂ (V-con t (Utils.HSindexArray as i))
          }
        }
    ; _ -> inj₁ userError
  }
BUILTIN chooseData = λ
  { (app (app (app (app (app (app (app⋆ base) (V-con pdata (ConstrDATA x₁ x₂))) v) _) _) _) _) → inj₂ v
  ; (app (app (app (app (app (app (app⋆ base) (V-con pdata (MapDATA x₁))) _) v) _) _) _) → inj₂ v
  ; (app (app (app (app (app (app (app⋆ base) (V-con pdata (ListDATA x₁))) _) _) v) _) _) → inj₂ v
  ; (app (app (app (app (app (app (app⋆ base) (V-con pdata (iDATA x₁))) _) _) _) v) _) → inj₂ v
  ; (app (app (app (app (app (app (app⋆ base) (V-con pdata (bDATA x₁))) _) _) _) _) v) → inj₂ v
  ; _ -> inj₁ userError
  }
BUILTIN constrData = λ
  { (app (app base (V-con integer i)) (V-con (list pdata) xs)) → do
     return (V-con pdata (ConstrDATA i xs))
  ; _ -> inj₁ userError
  }
BUILTIN mapData = λ
  { (app base (V-con (list (pair pdata pdata)) xs)) → do
     return (V-con pdata (MapDATA xs))
  ; _ -> inj₁ userError
  }
BUILTIN listData = λ
  { (app base (V-con (list pdata) xs)) → do
     return (V-con pdata (ListDATA xs))
  ; _ -> inj₁ userError
  }
BUILTIN unConstrData = λ
  { (app base (V-con pdata (ConstrDATA i xs))) → inj₂ (V-con (pair integer (list pdata)) (i , xs))
  ; _ -> inj₁ userError
  }
BUILTIN unMapData = λ
  { (app base (V-con pdata (MapDATA xs))) → inj₂ (V-con (list (pair pdata pdata)) xs)
  ; _ -> inj₁ userError
  }
BUILTIN unListData = λ
  { (app base (V-con pdata (ListDATA xs))) → inj₂ (V-con (list pdata) xs)
  ; _ -> inj₁ userError
  }
BUILTIN equalsData = λ
  {
    (app (app base (V-con pdata x)) (V-con pdata y)) → inj₂ (V-con bool (eqDATA x y))
  ;  _ -> inj₁ userError
  }
BUILTIN mkPairData = λ
  { (app (app base (V-con pdata x)) (V-con pdata y)) → inj₂ (V-con (pair pdata pdata) (x , y))
  ; _ -> inj₁ userError
  }
BUILTIN mkNilData = λ
  { (app base (V-con unit tt)) → inj₂ (V-con (list pdata) [])
  ; _ -> inj₁ userError
  }
BUILTIN mkNilPairData = λ
  { (app base (V-con unit tt)) -> inj₂ (V-con (list (pair pdata pdata)) [])
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-add = λ
  { (app (app base (V-con bls12-381-g1-element e)) (V-con bls12-381-g1-element e')) -> inj₂ (V-con bls12-381-g1-element (BLS12-381-G1-add e e'))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-neg = λ
  { (app base (V-con bls12-381-g1-element e)) -> inj₂ (V-con bls12-381-g1-element (BLS12-381-G1-neg e))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-scalarMul = λ
  { (app (app base (V-con integer i)) (V-con bls12-381-g1-element e)) -> inj₂ (V-con bls12-381-g1-element (BLS12-381-G1-scalarMul i e))
  ;  _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-equal = λ
  { (app (app base (V-con bls12-381-g1-element e)) (V-con bls12-381-g1-element e')) -> inj₂ (V-con bool (BLS12-381-G1-equal e e'))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-hashToGroup = λ
  { (app (app base (V-con bytestring msg)) (V-con bytestring dst)) -> case BLS12-381-G1-hashToGroup msg dst of λ
     { (just p) -> inj₂ (V-con bls12-381-g1-element p)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-compress = λ
  { (app base (V-con bls12-381-g1-element e)) -> inj₂ (V-con bytestring (BLS12-381-G1-compress e))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-uncompress = λ
  { (app base (V-con bytestring b)) -> case  BLS12-381-G1-uncompress b of λ
     { (just e) -> inj₂ (V-con bls12-381-g1-element e)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-add = λ
  { (app (app base (V-con bls12-381-g2-element e)) (V-con bls12-381-g2-element e')) -> inj₂ (V-con bls12-381-g2-element (BLS12-381-G2-add e e'))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-neg = λ
  { (app base (V-con bls12-381-g2-element e)) -> inj₂ (V-con bls12-381-g2-element (BLS12-381-G2-neg e))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-scalarMul = λ
  { (app (app base (V-con integer i)) (V-con bls12-381-g2-element e)) -> inj₂ (V-con bls12-381-g2-element (BLS12-381-G2-scalarMul i e))
  ;  _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-equal = λ
  { (app (app base (V-con bls12-381-g2-element e)) (V-con bls12-381-g2-element e')) -> inj₂ (V-con bool (BLS12-381-G2-equal e e'))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-hashToGroup = λ
  { (app (app base (V-con bytestring msg)) (V-con bytestring dst)) -> case BLS12-381-G2-hashToGroup msg dst of λ
     { (just p) -> inj₂ (V-con bls12-381-g2-element p)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-compress = λ
  { (app base (V-con bls12-381-g2-element e)) -> inj₂ (V-con bytestring (BLS12-381-G2-compress e))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-uncompress = λ
  { (app base (V-con bytestring b)) -> case  BLS12-381-G2-uncompress b of λ
     { (just e) -> inj₂ (V-con bls12-381-g2-element e)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-millerLoop = λ
  { (app (app base (V-con bls12-381-g1-element e1)) (V-con bls12-381-g2-element e2)) -> inj₂ (V-con bls12-381-mlresult (BLS12-381-millerLoop e1 e2))
  ;  _ -> inj₁ userError
  }
BUILTIN bls12-381-mulMlResult = λ
  { (app (app base (V-con bls12-381-mlresult r)) (V-con bls12-381-mlresult r')) -> inj₂ (V-con bls12-381-mlresult (BLS12-381-mulMlResult r r'))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-finalVerify = λ
  { (app (app base (V-con bls12-381-mlresult r)) (V-con bls12-381-mlresult r')) -> inj₂ (V-con bool (BLS12-381-finalVerify r r'))
  ; _ -> inj₁ userError
  }
BUILTIN keccak-256 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (KECCAK-256 b))
  ; _ -> inj₁ userError
  }
BUILTIN blake2b-224 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (BLAKE2B-224 b))
  ; _ -> inj₁ userError
  }
BUILTIN byteStringToInteger = λ
  { (app (app base (V-con bool e)) (V-con bytestring s)) -> inj₂ (V-con integer (BStoI e s))
  ; _ -> inj₁ userError
  }
BUILTIN integerToByteString = λ
  { (app (app (app base (V-con bool e)) (V-con integer w)) (V-con integer n)) -> case ItoBS e w n of λ
      { (just s) -> inj₂ (V-con bytestring s)
      ; nothing -> inj₁ userError
      }
  ; _ -> inj₁ userError
  }
BUILTIN andByteString = λ
  { (app (app (app base (V-con bool b)) (V-con bytestring s)) (V-con bytestring s')) -> inj₂ (V-con bytestring (andBYTESTRING b s s'))
  ; _ -> inj₁ userError
  }
BUILTIN orByteString = λ
  { (app (app (app base (V-con bool b)) (V-con bytestring s)) (V-con bytestring s')) -> inj₂ (V-con bytestring (orBYTESTRING b s s'))
  ; _ -> inj₁ userError
  }
BUILTIN xorByteString = λ
  { (app (app (app base (V-con bool b)) (V-con bytestring s)) (V-con bytestring s')) -> inj₂ (V-con bytestring (xorBYTESTRING b s s'))
  ; _ -> inj₁ userError
  }
BUILTIN complementByteString = λ
  { (app base (V-con bytestring s)) -> inj₂ (V-con bytestring (complementBYTESTRING s))
  ; _ -> inj₁ userError
  }
BUILTIN readBit = λ
  { (app (app base (V-con bytestring s)) (V-con integer i)) -> case readBIT s i of λ
     { (just r) -> inj₂ (V-con bool r)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN writeBits = λ
  { (app (app (app base (V-con bytestring s)) (V-con (list integer) ps)) (V-con bool u)) ->
     case writeBITS s (toList ps) u of λ
       { (just r) -> inj₂ (V-con bytestring r)
       ; nothing  -> inj₁ userError
       }
  ; _ -> inj₁ userError
  }
BUILTIN replicateByte = λ
  { (app (app base (V-con integer l)) (V-con integer w)) -> case replicateBYTE l w of λ
     { (just r) -> inj₂ (V-con bytestring r)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN shiftByteString = λ
  { (app (app base (V-con bytestring s)) (V-con integer i)) -> inj₂ (V-con bytestring (shiftBYTESTRING s i))
  ; _ -> inj₁ userError
  }
BUILTIN rotateByteString = λ
  { (app (app base (V-con bytestring s)) (V-con integer i)) -> inj₂ (V-con bytestring (rotateBYTESTRING s i))
  ; _ -> inj₁ userError
  }
BUILTIN countSetBits  = λ
  { (app base (V-con bytestring s)) -> inj₂ (V-con integer (countSetBITS s))
  ; _ -> inj₁ userError
  }
BUILTIN findFirstSetBit  = λ
  { (app base (V-con bytestring s)) -> inj₂ (V-con integer (findFirstSetBIT s))
  ; _ -> inj₁ userError
  }
BUILTIN ripemd-160 = λ
  { (app base (V-con bytestring b)) -> inj₂ (V-con bytestring (RIPEMD-160 b))
  ; _ -> inj₁ userError
  }
BUILTIN expModInteger = λ
  { (app (app (app base (V-con integer b)) (V-con integer e)) (V-con integer m)) -> case expModINTEGER b e m of λ
     { (just r) -> inj₂ (V-con integer r)
     ; nothing  -> inj₁ userError
     }
  ; _ -> inj₁ userError
  }
BUILTIN dropList = λ
  { (app (app (app⋆ base) (V-con integer n)) (V-con (list t) l)) → inj₂ (V-con (list t) (dropLIST n l))
  ; _ -> inj₁ userError
  }
BUILTIN bls12-381-G1-multiScalarMul = λ
  { (app (app base (V-con (list integer) is)) (V-con (list bls12-381-g1-element) es)) -> case BLS12-381-G1-multiScalarMul (toList is) (toList es) of λ
     { (just r) -> inj₂ (V-con bls12-381-g1-element r)
     ; nothing  -> inj₁ userError
     }
  ;  _ -> inj₁ userError
  }
BUILTIN bls12-381-G2-multiScalarMul = λ
  { (app (app base (V-con (list integer) is)) (V-con (list bls12-381-g2-element) es)) -> case BLS12-381-G2-multiScalarMul (toList is) (toList es) of λ
     { (just r) -> inj₂ (V-con bls12-381-g2-element r)
     ; nothing  -> inj₁ userError
     }
  ;  _ -> inj₁ userError
  }

-- Take an apparently more general index and show that it is a fully applied builtin.
mkFullyAppliedBuiltin : ∀ { b }
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → BApp b pt pa
  → fullyAppliedBuiltin b
mkFullyAppliedBuiltin {b} {pt = pt} {pa = pa} bt with trans (sym (+-identityʳ _)) (∔2+ pt) | trans (sym (+-identityʳ _)) (∔2+ pa)
... | refl | refl with unique∔ pt (alldone (fv (signature b))) | unique∔ pa (alldone (args♯ (signature b)))
... | refl | refl = bt

BUILTIN' : ∀ b
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → BApp b pt pa
  → Either RuntimeError Value
BUILTIN' b bt =  BUILTIN b (mkFullyAppliedBuiltin bt)

ival : Builtin → Value
ival b = V-I b base

pushValueFrames : Stack Frame → Stack Value → Stack Frame
pushValueFrames s ε = s
pushValueFrames s (vs , v) = pushValueFrames (s , -·v v) vs

lookup? : ∀{A} → ℕ → List A → Maybe A
lookup? n [] = nothing
lookup? zero (x ∷ xs) = just x
lookup? (suc n) (x ∷ xs) = lookup? n xs

lookup?-deterministic : {A : Set} {x₁ x₂ : A} → (n : ℕ) → (xs : List A) → lookup? n xs ≡ just x₁ → lookup? n xs ≡ just x₂ → x₁ ≡ x₂
lookup?-deterministic n xs p₁ p₂ with trans (sym p₁) p₂
... | refl = refl

step : State → State
step (s ; ρ ▻ ` x)               = s ◅ lookup ρ x
step (s ; ρ ▻ ƛ t)               = s ◅ V-ƛ ρ t
step (s ; ρ ▻ (t · u))           = (s , -· ρ u) ; ρ ▻ t
step (s ; ρ ▻ force t)           = (s , force-) ; ρ ▻ t
step (s ; ρ ▻ delay t)           = s ◅ V-delay ρ t
step (s ; ρ ▻ con (tmCon t c))   = s ◅ V-con t c
step (s ; ρ ▻ constr i [])       = s ◅ V-constr i ε
step (s ; ρ ▻ constr i (x ∷ xs)) = (s , constr- i ε ρ xs); ρ ▻ x
step (s ; ρ ▻ case t ts)         = (s , case- ρ ts) ; ρ ▻ t
step (s ; ρ ▻ builtin b)         = s ◅ ival b
step (s ; ρ ▻ error)             = ◆

step (ε ◅ v)                               = □ v
step ((s , -· ρ u) ◅ v)                    = (s , (v ·-)) ; ρ ▻ u
step ((s , -·v v) ◅ vf)                    = (s , vf ·-) ◅ v
step ((s , (V-ƛ ρ t ·-)) ◅ v)              = s ; ρ ∷ v ▻ t
step ((s , (V-con _ _   ·-)) ◅ v)          = ◆ -- constant in function position
step ((s , (V-delay _ _ ·-)) ◅ v)          = ◆ -- delay in function position
step ((s , (V-IΠ b bapp ·-)) ◅ v)          = ◆ -- delayed builtin in function position
step ((s , (V-constr i vs ·-)) ◅ v)        = ◆ -- SOP in function position
step ((s , force-) ◅ V-IΠ b bapp)          = s ◅ V-I b (app⋆ bapp)
step ((s , force-) ◅ V-delay ρ t)          = step (s ; ρ ▻ t)
step ((s , force-) ◅ V-ƛ _ _)              = ◆ -- lambda in delay position
step ((s , force-) ◅ V-con _ _)            = ◆ -- constant in delay position
step ((s , force-) ◅ V-I⇒ b bapp)          = ◆ -- function in delay position
step ((s , force-) ◅ V-constr i vs)        = ◆ -- SOP in delay position
step ((s , constr- i vs ρ []) ◅ v)         = s ◅ V-constr i (vs , v)
step ((s , constr- i vs ρ (t ∷ ts)) ◅ v)   = (s , constr- i (vs , v) ρ ts); ρ ▻ t
step ((s , case- ρ ts) ◅ V-constr i vs)    = maybe (pushValueFrames s vs ; ρ ▻_) ◆ (lookup? i ts)
step ((s , case- ρ ts) ◅ V-ƛ _ _)          = ◆ -- case of lambda
step ((s , case- ρ ts) ◅ V-con _ _)        = ◆ -- case of constant
step ((s , case- ρ ts) ◅ V-delay _ _)      = ◆ -- case of delay
step ((s , case- ρ ts) ◅ V-I⇒ _ _)         = ◆ -- case of builtin value
step ((s , case- ρ ts) ◅ V-IΠ _ _)         = ◆ -- case of delayed builtin
step ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ v) = either (BUILTIN' b (app bapp v)) (λ _ → ◆) (s ◅_)
step ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ v) = s ◅ V-I b (app bapp v)

step (□ v)               = □ v
step ◆                   = ◆

stepper : ℕ → (t : State) → Either RuntimeError State
stepper 0       s = inj₁ gasError
stepper (suc n) s with step s
... | (s ; ρ ▻ t) = stepper n (s ; ρ ▻ t)
... | (s ◅ v)     = stepper n (s ◅ v)
... | (□ v)       = return (□ v)
... | ◆           = return ◆
