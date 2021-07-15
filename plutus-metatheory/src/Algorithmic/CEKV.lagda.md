# CEK machine that discharges builtin args

```
{-# OPTIONS --rewriting #-}

module Algorithmic.CEKV where

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Function hiding (_∋_)
open import Data.Product using (proj₁;proj₂)
import Data.List as L
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_;Σ) renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false)
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Debug.Trace as Debug
open import Utils

open import Type
open import Type.BetaNormal
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Utils using (decIf;just;nothing)

data Env : Ctx ∅ → Set

ITel : Builtin → ∀{Φ} → Ctx Φ → SubNf Φ ∅ → Set
data Value : (A : ∅ ⊢Nf⋆ *) → Set where
  V-ƛ : ∀ {Γ}{A B : ∅ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
    → Env Γ
    → Value (A ⇒ B)

  V-Λ : ∀ {Γ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
    → Env Γ
    → Value (Π B)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → Value (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
   → Value (μ A B)

  V-con : {tcn : TyCon}
    → (cn : TermCon {∅} (con tcn))
    → Value (con tcn)

  V-I⇒ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{A : Φ' ⊢Nf⋆ *}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅)
    → (p : (Δ , A) ≤C' Γ)
    → ITel b Δ σ
    → (t : ∅ ⊢ subNf σ (<C'2type (skip p) C))
    → Value (subNf σ (<C'2type (skip p) C))

  V-IΠ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{K}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅) -- could try one at a time
      (p : (Δ ,⋆ K) ≤C' Γ)
    → ITel b Δ σ
    → (t : ∅ ⊢ subNf σ (<C'2type (skip⋆ p) C))
    → Value (subNf σ (<C'2type (skip⋆ p) C))

ITel b ∅       σ = ⊤
ITel b (Γ ,⋆ J) σ = ITel b Γ (σ ∘ S) × ∅ ⊢Nf⋆ J
ITel b (Γ , A)  σ = ITel b Γ σ × Value (subNf σ A)

-- ITel is very similar to Env...
-- The most significant difference is that envs don't contain types
-- if they did we could perhaps delay type substitutions too...

data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ

convValue : ∀{A A'}(p : A ≡ A') → Value A → Value A'
convValue refl v = v

data Error : ∅ ⊢Nf⋆ * → Set where
  -- an actual error term
  E-error : (A : ∅ ⊢Nf⋆ *) → Error A

discharge : ∀{A} → Value A → ∅ ⊢ A

env2ren : ∀{Γ} → Env Γ → Sub (ne ∘ `) Γ ∅
env2ren (ρ ∷ V) Z     = conv⊢ refl (sym (subNf-id _)) (discharge V)
env2ren (ρ ∷ C)                   (S x) = env2ren ρ x

dischargeBody : ∀{Γ A B} → Γ , A ⊢ B → Env Γ → ∅ , A ⊢ B
dischargeBody M ρ = conv⊢
  (cong (∅ ,_) (subNf-id _))
  (subNf-id _)
  (sub (ne ∘ `) (exts (ne ∘ `) (env2ren ρ)) M)

dischargeBody⋆ : ∀{Γ K A} → Γ ,⋆ K ⊢ A → Env Γ → ∅ ,⋆ K ⊢ A
dischargeBody⋆ {A = A} M ρ = conv⊢
  refl
  (trans
    (subNf-cong
      {f = extsNf (ne ∘ `)}
      {g = ne ∘ `}
      (λ{ Z → refl; (S α) → refl})
      A)
    (subNf-id A))
  (sub (extsNf (ne ∘ `)) (exts⋆ (ne ∘ `) (env2ren ρ)) M)

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c
discharge (V-I⇒ _ _ _ _ _ _ _ t) = t
discharge (V-IΠ _ _ _ _ _ _ _ t) = t

VTel : ∀ Δ → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)(As : L.List (Δ ⊢Nf⋆ *)) → Set
VTel Δ σ L.[]       = ⊤
VTel Δ σ (A L.∷ As) = Value (subNf σ A) × VTel Δ σ As

extendVTel : ∀{Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vs : VTel Δ σ Bs)
    → ∀{C}(v : Value (subNf σ C))
    → (p : Bs L.++ (C L.∷ L.[]) ≡ As)
    → VTel Δ σ As
extendVTel L.[] σ vs v refl = v ,, _
extendVTel (B L.∷ Bs) σ (v ,, vs) v' refl = v ,, extendVTel Bs σ vs v' refl

BUILTIN : (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vtel : VTel Δ σ As)
      -----------------------------
    → Value (subNf σ C) ⊎ ∅ ⊢Nf⋆ *
BUILTIN addInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i + i')))
BUILTIN subtractInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i - i')))
BUILTIN multiplyInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i ** i')))
BUILTIN divideInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (div i i'))))
BUILTIN quotientInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (quot i i'))))
BUILTIN remainderInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (rem i i'))))
BUILTIN modInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i <? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN
  lessThanEqualsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i ≤? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN greaterThanInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i I>? i')
        (inj₁ (V-con (bool true)))
        (inj₁ (V-con (bool false)))
BUILTIN
  greaterThanEqualsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i I≥? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN equalsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i ≟ i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN concatenate σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  inj₁ (V-con (bytestring (concat b b')))
BUILTIN takeByteString σ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (take i b)))
BUILTIN dropByteString σ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (drop i b)))
BUILTIN lessThanByteString σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = inj₁ (V-con (bool (B< b b')))
BUILTIN greaterThanByteString σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = inj₁ (V-con (bool (B> b b')))
BUILTIN sha2-256 σ (V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (SHA2-256 b)))
BUILTIN sha3-256 σ (V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (SHA3-256 b)))
BUILTIN
  verifySignature
  σ
  (V-con (bytestring k)
   ,,
   V-con (bytestring d)
   ,,
   V-con (bytestring c)
   ,,
   tt) with (verifySig k d c)
... | just b = inj₁ (V-con (bool b))
... | nothing = inj₂ (con bool)

BUILTIN equalsByteString σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = inj₁ (V-con (bool (equals b b')))

BUILTIN ifThenElse σ (VF ,, VT ,, V-con (bool false) ,, tt) = inj₁ VF
BUILTIN ifThenElse σ (VF ,, VT ,, V-con (bool true) ,, tt) = inj₁ VT
BUILTIN charToString σ (V-con (char c) ,, tt) = inj₁ (V-con (string (primStringFromList L.[ c ])))
BUILTIN append σ (V-con (string s) ,, V-con (string t) ,, tt) = inj₁ (V-con (string (primStringAppend s t)))
BUILTIN trace σ (V-con (string s) ,, tt) = inj₁ (V-con (Debug.trace s unit))

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Value (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B)
            (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
            (μ A B)

data Stack (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  ε   : Stack T T
  _,_ : ∀{H1 H2} → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → Value H → State T
  □     : Value T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

ival : ∀ b → Value (itype b)
ival addInteger = V-I⇒ addInteger {Γ = proj₁ (proj₂ (ISIG addInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG addInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin addInteger)
ival subtractInteger = V-I⇒ subtractInteger {Γ = proj₁ (proj₂ (ISIG subtractInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG subtractInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin subtractInteger)
ival multiplyInteger = V-I⇒ multiplyInteger {Γ = proj₁ (proj₂ (ISIG multiplyInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG multiplyInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin multiplyInteger)
ival divideInteger = V-I⇒ divideInteger {Γ = proj₁ (proj₂ (ISIG divideInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG divideInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin divideInteger)
ival quotientInteger = V-I⇒ quotientInteger {Γ = proj₁ (proj₂ (ISIG quotientInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG quotientInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin quotientInteger)
ival remainderInteger = V-I⇒ remainderInteger {Γ = proj₁ (proj₂ (ISIG remainderInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG remainderInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin remainderInteger)
ival modInteger = V-I⇒ modInteger {Γ = proj₁ (proj₂ (ISIG modInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG modInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin modInteger)
ival lessThanInteger = V-I⇒ lessThanInteger {Γ = proj₁ (proj₂ (ISIG lessThanInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin lessThanInteger)
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger {Γ = proj₁ (proj₂ (ISIG lessThanEqualsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanEqualsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin lessThanEqualsInteger)
ival greaterThanInteger = V-I⇒ greaterThanInteger {Γ = proj₁ (proj₂ (ISIG greaterThanInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin greaterThanInteger)
ival greaterThanEqualsInteger = V-I⇒ greaterThanEqualsInteger {Γ = proj₁ (proj₂ (ISIG greaterThanEqualsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanEqualsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin greaterThanEqualsInteger)
ival equalsInteger = V-I⇒ equalsInteger {Γ = proj₁ (proj₂ (ISIG equalsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG equalsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin equalsInteger)
ival concatenate = V-I⇒ concatenate {Γ = proj₁ (proj₂ (ISIG concatenate))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG concatenate))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin concatenate)
ival takeByteString = V-I⇒ takeByteString {Γ = proj₁ (proj₂ (ISIG takeByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG takeByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin takeByteString)
ival dropByteString = V-I⇒ dropByteString {Γ = proj₁ (proj₂ (ISIG dropByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG dropByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin dropByteString)
ival lessThanByteString = V-I⇒ lessThanByteString {Γ = proj₁ (proj₂ (ISIG lessThanByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin lessThanByteString)
ival greaterThanByteString = V-I⇒ greaterThanByteString {Γ = proj₁ (proj₂ (ISIG greaterThanByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin greaterThanByteString)
ival sha2-256 = V-I⇒ sha2-256 {Γ = proj₁ (proj₂ (ISIG sha2-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha2-256))} refl refl refl (λ()) base tt (ibuiltin sha2-256)
ival sha3-256 = V-I⇒ sha3-256 {Γ = proj₁ (proj₂ (ISIG sha3-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha3-256))} refl refl refl (λ()) base tt (ibuiltin sha3-256)
ival verifySignature = V-I⇒ verifySignature {Γ = proj₁ (proj₂ (ISIG verifySignature))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG verifySignature))} refl refl refl (λ()) (≤Cto≤C' (skip (skip base))) tt (ibuiltin verifySignature)
ival equalsByteString = V-I⇒ equalsByteString {Γ = proj₁ (proj₂ (ISIG equalsByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG equalsByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin equalsByteString)
ival ifThenElse = V-IΠ ifThenElse {Γ = proj₁ (proj₂ (ISIG ifThenElse))}{C = proj₂ (proj₂ (ISIG ifThenElse))} refl refl refl (λ()) (≤Cto≤C' (skip (skip (skip base)))) tt (ibuiltin ifThenElse)
ival charToString = V-I⇒ charToString {Γ = proj₁ (proj₂ (ISIG charToString))}{C = proj₂ (proj₂ (ISIG charToString))} refl refl refl (λ()) base tt (ibuiltin charToString)
ival append = V-I⇒ append {Γ = proj₁ (proj₂ (ISIG append))}{C = proj₂ (proj₂ (ISIG append))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin append)
ival trace = V-I⇒ trace {Γ = proj₁ (proj₂ (ISIG trace))}{C = proj₂ (proj₂ (ISIG trace))} refl refl refl (λ()) base tt (ibuiltin trace)


IBUILTIN : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      (σ : SubNf Φ ∅)
    → (tel : ITel b Γ σ)
      -----------------------------
    → Value (subNf σ C) ⊎ Error (subNf σ C)
IBUILTIN addInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i + j)))
IBUILTIN subtractInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i - j)))
IBUILTIN multiplyInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i ** j)))
IBUILTIN divideInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (div i j)))
... | yes p = inj₂ (E-error (con integer))-- divide by zero
IBUILTIN quotientInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (quot i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN remainderInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (rem i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN modInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (mod i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN lessThanInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i <? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN lessThanEqualsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i ≤? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN greaterThanInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i I>? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN greaterThanEqualsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i I≥? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN equalsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i ≟ j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN concatenate σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) =
  inj₁ (V-con (bytestring (concat b b')))
IBUILTIN takeByteString σ ((tt ,, V-con (integer i)) ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (take i b)))
IBUILTIN dropByteString σ ((tt ,, V-con (integer i)) ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (drop i b)))
IBUILTIN lessThanByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (B< b b')))
IBUILTIN greaterThanByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (B> b b')))
IBUILTIN sha2-256 σ (tt ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (SHA2-256 b)))
IBUILTIN sha3-256 σ (tt ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (SHA3-256 b)))
IBUILTIN verifySignature σ ((((tt ,, V-con (bytestring k)) ,, V-con (bytestring d))) ,, V-con (bytestring c)) with verifySig k d c
... | just false = inj₁ (V-con (bool false))
... | just true = inj₁ (V-con (bool true))
... | nothing = inj₂ (E-error (con bool)) -- not sure what this is for
IBUILTIN equalsByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (equals b b')))
IBUILTIN ifThenElse σ ((((tt ,, A) ,, V-con (bool true)) ,, t) ,, f) = inj₁ t
IBUILTIN ifThenElse σ ((((tt ,, A) ,, V-con (bool false)) ,, t) ,, f) = inj₁ f
IBUILTIN charToString σ (tt ,, V-con (char c)) =
  inj₁ (V-con (string (primStringFromList L.[ c ])))
IBUILTIN append σ ((tt ,, V-con (string s)) ,, V-con (string s')) = inj₁ (V-con (string (primStringAppend s s')))
IBUILTIN trace σ _ = inj₁ (V-con unit)

IBUILTIN' : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}
    → (p : Φ ≡ Φ')
    → (q : substEq Ctx p Γ ≡ Γ')
      (σ : SubNf Φ' ∅)
    → (tel : ITel b Γ' σ)
    → (C' : Φ' ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
      -----------------------------
    → Value (subNf σ C') ⊎ Error (subNf σ C')
    
IBUILTIN' b refl refl σ tel _ refl = IBUILTIN b σ tel

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)             = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)             = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))         = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)             = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A))        = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c) = s ◅ V-con c
step (s ; ρ ▻ ibuiltin b) = s ◅ ival b
  -- ^ this is constant here, so we drop the env
step (s ; ρ ▻ error A) = ◆ A
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {A = A}{B = B}) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step ((s , (V-I⇒ b p q r σ base vs t ·-)) ◅ v) with IBUILTIN' b p q σ (vs ,, v) _ r
... | inj₁ v' = s ◅ v'
... | inj₂ (E-error B) = ◆ B
  
step ((s , (V-I⇒ b p q r σ (skip⋆ p') vs t ·-)) ◅ v) =
  s ◅ V-IΠ b p q r σ p' (vs ,, v) (t · discharge v)
step ((s , (V-I⇒ b p q r σ (skip p') vs t ·-)) ◅ v) =
  s ◅ V-I⇒ b p q r σ p' (vs ,, v) (t · discharge v)
step ((s , -·⋆ A) ◅ V-IΠ b {C = C} p q r σ base vs t) with IBUILTIN' b p q (subNf-cons σ A) (vs ,, A) _ r
... | inj₁ v' = s ◅ convValue (subNf-cons-[]Nf C) v'
... | inj₂ (E-error B) = ◆ B
step ((s , -·⋆ A) ◅ V-IΠ b {C = C} p q r σ (skip⋆ p') vs t) = s ◅ convValue (sym (Πlem p' A C σ)) (V-IΠ b {C = C} p q r (subNf-cons σ A) p' (vs ,, A) (conv⊢ refl (Πlem p' A C σ) (t ·⋆ A)))
step ((s , -·⋆ A) ◅ V-IΠ b {C = C} p q r σ (skip p') vs t) = s ◅ convValue (sym (⇒lem p' σ C)) (V-I⇒ b p q r (subNf-cons σ A) p' (vs ,, A) (conv⊢ refl (⇒lem p' σ C) (t ·⋆ A) ))
step (□ V) = □ V
step (◆ A) = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)
