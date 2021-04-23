```
{-# OPTIONS --termination-depth=1000 #-}

module Algorithmic.ReductionEC where
```

## Imports

```
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function hiding (_∋_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_) renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (zero)
open import Data.Unit using (tt)
import Debug.Trace as Debug


open import Type
import Type.RenamingSubstitution as T
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Utils
open import Data.Maybe using (just;from-just)
open import Data.String using (String)
```

## Values

```

-- something very much like a substitution
-- labelled by a builtin and given a first order presentation
ITel : Builtin → ∀{Φ} → Ctx Φ → SubNf Φ ∅ → Set

data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set

data BV (b : Builtin) : ∀{A} → ∅ ⊢ A → Set where
  base : BV b (ibuiltin b)
  step : ∀{A B}
    → {t : ∅ ⊢ A ⇒ B} → BV b t → Value t
    → {u : ∅ ⊢ A} → Value u → BV b (t · u)
  step⋆ : ∀{B}
    → {t : ∅ ⊢ Π B} → BV b t → Value t
    → {A : ∅ ⊢Nf⋆ K} → BV b (t ·⋆ A)

data Value where
  V-ƛ : {A B : ∅ ⊢Nf⋆ *}
    → (M : ∅ , A ⊢ B)
      ---------------------------
    → Value (ƛ M)

  V-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : ∅ ,⋆ K ⊢ B)
      ----------------
    → Value (Λ M)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢  _}
   → Value M
   → Value (wrap A B M)

  V-con : ∀{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value (con cn)

  -- It is not necessary to index by the builtin, I could instead index
  -- by a context which is extracted from the builtin in the base case,
  -- but is it helpful to have it on the top level?

  V-I⇒ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{A : Φ' ⊢Nf⋆ *}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅)
    → (p : (Δ , A) ≤C' Γ)
    → ITel b Δ σ
    → ∀ {A'}
    → A' ≡ subNf σ (<C'2type (skip p) C)
    → (t : ∅ ⊢ A')
    → BV b t
    → Value t

  V-IΠ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{K}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅) -- could try one at a time
      (p : (Δ ,⋆ K) ≤C' Γ)
    → ITel b Δ σ
    → ∀{A}
    → A ≡ subNf σ (<C'2type (skip⋆ p) C)
    → (t : ∅ ⊢ A)
    → BV b t
    → Value t

ITel b ∅       σ = ⊤
ITel b (Γ ,⋆ J) σ = ITel b Γ (σ ∘ S) × ∅ ⊢Nf⋆ J
ITel b (Γ , A) σ = ITel b Γ σ × Σ (∅ ⊢ subNf σ A) Value

convBV : ∀{b A A'}{t : ∅ ⊢ A}(p : A ≡ A') → BV b t → BV b (conv⊢ refl p t)
convBV refl bv = bv

deval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢ A
deval {u = u} _ = u

tval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢Nf⋆ *
tval {A = A} _ = A
```

```
voidVal : Value (con unit)
voidVal = V-con unit
```

```
data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
```

```
convVal :  ∀ {A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → Value t → Value (conv⊢ refl q t)
convVal refl v = v
```

```
IBUILTIN : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      (σ : SubNf Φ ∅)
    → (tel : ITel b Γ σ)
      -----------------------------
    → Σ (∅ ⊢ subNf σ C) λ t → Value t ⊎ Error t 
      -- ^ should be val or error to avoid throwing away work
IBUILTIN addInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i + j)))
IBUILTIN subtractInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i - j)))
IBUILTIN multiplyInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i ** j)))
IBUILTIN divideInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₁ (V-con (integer (div i j)))
... | yes p = _ ,, inj₂ E-error -- divide by zero
IBUILTIN quotientInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₁ (V-con (integer (quot i j)))
... | yes p = _ ,, inj₂ E-error -- divide by zero
IBUILTIN remainderInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₁ (V-con (integer (rem i j)))
... | yes p = _ ,, inj₂ E-error -- divide by zero
IBUILTIN modInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₁ (V-con (integer (mod i j)))
... | yes p = _ ,, inj₂ E-error -- divide by zero
IBUILTIN lessThanInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i <? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))

IBUILTIN lessThanEqualsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i ≤? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN greaterThanInteger σ  ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i I>? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN greaterThanEqualsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i I≥? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN equalsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j))  with i ≟ j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN concatenate σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bytestring (concat b b')))
IBUILTIN takeByteString σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (take i b)))
IBUILTIN dropByteString σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (drop i b)))
IBUILTIN lessThanByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (B< b b')))
IBUILTIN greaterThanByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (B> b b')))
IBUILTIN sha2-256 σ (tt ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (SHA2-256 b)))
IBUILTIN sha3-256 σ (tt ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (SHA3-256 b)))
IBUILTIN verifySignature σ (((tt ,, _ ,, V-con (bytestring k)) ,, _ ,, V-con (bytestring d)) ,, _ ,, V-con (bytestring c)) with verifySig k d c
... | just b = _ ,, inj₁ (V-con (bool b))
... | nothing = _ ,, inj₂ E-error -- not sure what this is for
IBUILTIN equalsByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (equals b b')))
IBUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, V-con (bool false)) ,, t) ,, f) =
  _ ,, inj₁ (proj₂ f)
IBUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, V-con (bool true)) ,, t) ,, f) =
  _ ,, inj₁ (proj₂ t)
IBUILTIN charToString σ (tt ,, _ ,, V-con (char c)) =
  _ ,, inj₁ (V-con (string (primStringFromList List.[ c ])))
IBUILTIN append σ ((tt ,, _ ,, V-con (string s)) ,, _ ,, V-con (string s')) =
  _ ,, inj₁ (V-con (string (primStringAppend s s')))
IBUILTIN trace σ _ = _ ,, inj₁ (V-con unit)

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
    → Σ (∅ ⊢ subNf σ C') λ t → Value t ⊎ Error t
    
IBUILTIN' b refl refl σ tel _ refl = IBUILTIN b σ tel
```

## Intrinsically Type Preserving Reduction

```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

data EC : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  []   : {A : ∅ ⊢Nf⋆ *} → EC A A
  _l·_ : {A B C : ∅ ⊢Nf⋆ *} → EC (A ⇒ B) C → ∅ ⊢ A → EC B C
  _·r_ : {A B C : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → EC A C → EC B C
  _·⋆_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}
    → EC (Π B) C → (A : ∅ ⊢Nf⋆ K) → EC (B [ A ]Nf) C
  wrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
    → EC (μ A B) C
  unwrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (μ A B) C
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
```

```
infix 2 _—→⋆_

data _—→⋆_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→⋆ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A —→⋆ N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) —→⋆ M

  β-sbuiltin :
      (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢Nf⋆ *}
    → (σ : SubNf Φ' ∅)
    → (p : Φ ≡ Φ')
    → (q : substEq Ctx p Γ ≡  Γ' , A)
    → (C' : Φ' ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
    → (t : ∅ ⊢ subNf σ A ⇒ subNf σ C')
    → (u : ∅ ⊢ subNf σ A)
    → (tel : ITel b Γ' σ)
    → (v : Value u)
      -----------------------------
    → t · u —→⋆ proj₁ (IBUILTIN' b p q σ (tel ,, u ,, v) C' r)

  β-sbuiltin⋆ :
      (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}{K}{A : ∅ ⊢Nf⋆ K}
    → (σ : SubNf Φ' ∅)
    → (p : Φ ≡ Φ' ,⋆ K)
    → (q : substEq Ctx p Γ ≡  (Γ' ,⋆ K))
    → (C' : Φ' ,⋆ K ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
    → (t : ∅ ⊢ subNf σ (Π C'))
    → (tel : ITel b Γ' σ)
      -----------------------------
    → t ·⋆ A —→⋆ conv⊢ refl (subNf-cons-[]Nf C') (proj₁ (IBUILTIN' b p q (subNf-cons σ A) (tel ,, A) C' r))

infix 2 _—→_

_[_]ᴱ : ∀{A B : ∅ ⊢Nf⋆ *} → EC B A → ∅ ⊢ A → ∅ ⊢ B
[]       [ L ]ᴱ = L
(E l· B) [ L ]ᴱ = E [ L ]ᴱ · B
(V ·r E) [ L ]ᴱ = deval V · E [ L ]ᴱ
(E ·⋆ A) [ L ]ᴱ = E [ L ]ᴱ ·⋆ A
wrap   E [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
unwrap E [ L ]ᴱ = unwrap (E [ L ]ᴱ)

_[_]ᶠ : ∀{A B : ∅ ⊢Nf⋆ *} → Frame B A → ∅ ⊢ A → ∅ ⊢ B
(-· M') [ L ]ᶠ = L · M' 
(V ·-)  [ L ]ᶠ = deval V · L
-·⋆ A   [ L ]ᶠ = L ·⋆ A
wrap-   [ L ]ᶠ = wrap _ _ L
unwrap- [ L ]ᶠ = unwrap L

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ruleEC : ∀{A B}{L L' : ∅ ⊢ B}
         → (E : EC A B)
         → L —→⋆ L'
         → ∀{M M' : ∅ ⊢ A}
         → M ≡ E [ L ]ᴱ
         → M' ≡ E [ L' ]ᴱ
           ----
         → M —→ M'

  ruleErr : ∀{A B}
          → (E : EC B A)
            ------------------------
          → E [ error A ]ᴱ —→ error B
```

```
data _—↠_ : {A A' : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A' → Set
  where

  refl—↠ : ∀{A}{M : ∅ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∅ ⊢Nf⋆ *}{M  M' M'' : ∅ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
```

```
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

  error :
      Error M
      -------
    → Progress M
```

```
ival : ∀ b → Value (ibuiltin b)
ival addInteger = V-I⇒ addInteger {Γ = proj₁ (proj₂ (ISIG addInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG addInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin addInteger) base
ival subtractInteger = V-I⇒ subtractInteger {Γ = proj₁ (proj₂ (ISIG subtractInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG subtractInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin subtractInteger) base
ival multiplyInteger = V-I⇒ multiplyInteger {Γ = proj₁ (proj₂ (ISIG multiplyInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG multiplyInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin multiplyInteger) base
ival divideInteger = V-I⇒ divideInteger {Γ = proj₁ (proj₂ (ISIG divideInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG divideInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin divideInteger) base
ival quotientInteger = V-I⇒ quotientInteger {Γ = proj₁ (proj₂ (ISIG quotientInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG quotientInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin quotientInteger) base
ival remainderInteger = V-I⇒ remainderInteger {Γ = proj₁ (proj₂ (ISIG remainderInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG remainderInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin remainderInteger) base
ival modInteger = V-I⇒ modInteger {Γ = proj₁ (proj₂ (ISIG modInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG modInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin modInteger) base
ival lessThanInteger = V-I⇒ lessThanInteger {Γ = proj₁ (proj₂ (ISIG lessThanInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin lessThanInteger) base
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger {Γ = proj₁ (proj₂ (ISIG lessThanEqualsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanEqualsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin lessThanEqualsInteger) base
ival greaterThanInteger = V-I⇒ greaterThanInteger {Γ = proj₁ (proj₂ (ISIG greaterThanInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin greaterThanInteger) base
ival greaterThanEqualsInteger = V-I⇒ greaterThanEqualsInteger {Γ = proj₁ (proj₂ (ISIG greaterThanEqualsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanEqualsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin greaterThanEqualsInteger) base
ival equalsInteger = V-I⇒ equalsInteger {Γ = proj₁ (proj₂ (ISIG equalsInteger))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG equalsInteger))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin equalsInteger) base
ival concatenate = V-I⇒ concatenate {Γ = proj₁ (proj₂ (ISIG concatenate))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG concatenate))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin concatenate) base
ival takeByteString = V-I⇒ takeByteString {Γ = proj₁ (proj₂ (ISIG takeByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG takeByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin takeByteString) base
ival dropByteString = V-I⇒ dropByteString {Γ = proj₁ (proj₂ (ISIG dropByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG dropByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin dropByteString) base
ival lessThanByteString = V-I⇒ lessThanByteString {Γ = proj₁ (proj₂ (ISIG lessThanByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG lessThanByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin lessThanByteString) base
ival greaterThanByteString = V-I⇒ greaterThanByteString {Γ = proj₁ (proj₂ (ISIG greaterThanByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG greaterThanByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin greaterThanByteString) base
ival sha2-256 = V-I⇒ sha2-256 {Γ = proj₁ (proj₂ (ISIG sha2-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha2-256))} refl refl refl (λ()) base tt refl (ibuiltin sha2-256) base
ival sha3-256 = V-I⇒ sha3-256 {Γ = proj₁ (proj₂ (ISIG sha3-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha3-256))} refl refl refl (λ()) base tt refl (ibuiltin sha3-256) base
ival verifySignature = V-I⇒ verifySignature {Γ = proj₁ (proj₂ (ISIG verifySignature))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG verifySignature))} refl refl refl (λ()) (≤Cto≤C' (skip (skip base))) tt refl (ibuiltin verifySignature) base
ival equalsByteString = V-I⇒ equalsByteString {Γ = proj₁ (proj₂ (ISIG equalsByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG equalsByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin equalsByteString) base
ival ifThenElse = V-IΠ ifThenElse {Γ = proj₁ (proj₂ (ISIG ifThenElse))}{C = proj₂ (proj₂ (ISIG ifThenElse))} refl refl refl (λ()) (≤Cto≤C' (skip (skip (skip base)))) tt refl (ibuiltin ifThenElse) base
ival charToString = V-I⇒ charToString {Γ = proj₁ (proj₂ (ISIG charToString))}{C = proj₂ (proj₂ (ISIG charToString))} refl refl refl (λ()) base tt refl (ibuiltin charToString) base
ival append = V-I⇒ append {Γ = proj₁ (proj₂ (ISIG append))}{C = proj₂ (proj₂ (ISIG append))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt refl (ibuiltin append) base
ival trace = V-I⇒ trace {Γ = proj₁ (proj₂ (ISIG trace))}{C = proj₂ (proj₂ (ISIG trace))} refl refl refl (λ()) base tt refl (ibuiltin trace) base

convValue : ∀{A A'}{t : ∅ ⊢ A}(p : A ≡ A') → Value (conv⊢ refl p t) → Value t
convValue refl v = v


progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress (ƛ M)        = done (V-ƛ M)
progress (M · M')     with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E)  = step (ruleErr (E l· M'))
... | error E-error = step (ruleErr ([] l· M'))
... | done V with progress M'
... | step (ruleEC E q refl refl) = step (ruleEC (V ·r E) q refl refl)
... | step (ruleErr E)  = step (ruleErr (V ·r E))
... | error E-error = step (ruleErr (V ·r []))
progress (.(ƛ M) · M') | done (V-ƛ M) | done W = step (ruleEC [] (β-ƛ W) refl refl)
progress (M · M') | done (V-I⇒ b p q r σ base x refl .M X) | done W = step (ruleEC [] (β-sbuiltin b σ p q _ r _ (deval W) x W) refl refl)
progress (M · M') | done V@(V-I⇒ b p q r σ (skip⋆ p₁) x refl .M X) | done W =
  done (V-IΠ b p q r σ p₁ (x ,, deval W ,, W) refl (M · deval W) (step X V W))
progress (M · M') | done V@(V-I⇒ b p q r σ (skip p₁) x refl .M X) | done W = 
  done (V-I⇒ b p q r σ p₁ (x ,, deval W ,, W) refl (M · deval W) (step X V W))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A) p refl refl)
... | step (ruleErr E)  = step (ruleErr (E ·⋆ A))
... | done (V-Λ M') = step (ruleEC [] β-Λ refl refl)
... | done (V-IΠ b p q r σ base x refl .M X) =
  step (ruleEC [] (β-sbuiltin⋆ b σ p q _ r M x) refl refl)
... | done V@(V-IΠ b {C = C} p q r σ (skip⋆ p₁) x refl .M X) =
  done (convValue (Πlem p₁ A C σ) (V-IΠ b {C = C} p q r (subNf-cons σ A) p₁ (x ,, A) refl (conv⊢ refl (Πlem p₁ A C σ) (M ·⋆ A)) (convBV _ (step⋆ X V))))
... | done V@(V-IΠ b {C = C} p q r σ (skip p₁) x refl .M X) =
  done (convValue (⇒lem p₁ σ C) (V-I⇒ b p q r (subNf-cons σ A) p₁ (x ,, A) refl (conv⊢ refl (⇒lem p₁ σ C) (M ·⋆ A) ) (convBV _ (step⋆ X V))))
... | error E-error     = step (ruleErr ([] ·⋆ A))
progress (wrap A B M) with progress M
... | done V            = done (V-wrap V)
... | step (ruleEC E p refl refl) = step (ruleEC (wrap E) p refl refl)
... | step (ruleErr E)  = step (ruleErr (wrap E))
... | error E-error     = step (ruleErr (wrap []))
progress (unwrap M) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E) p refl refl)
... | step (ruleErr E) = step (ruleErr (unwrap E))
... | done (V-wrap V) = step (ruleEC [] (β-wrap V) refl refl)
... | error E-error = step (ruleErr (unwrap []))
progress (con c)      = done (V-con c)
progress (ibuiltin b) = done (ival b)
progress (error A)    = error E-error

_↓ : ∀{A} → ∅ ⊢ A → Set
M ↓ = ∃ λ M' → M —→⋆ M'

-- progress in disguise

lemma51 : ∀{A}(M : ∅ ⊢ A)
        → Value M
        ⊎ ∃ λ B
        → ∃ λ (E : EC A B)
        → ∃ λ (L : ∅ ⊢ B)
        → (L ↓ ⊎ Error L)
        × M ≡ E [ L ]ᴱ 
lemma51 (ƛ M) = inj₁ (V-ƛ M)
lemma51 (M · M') with lemma51 M
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E l· M' ,, L ,, p ,, cong (_· M') q)
... | inj₁ VM with lemma51 M'
lemma51 (.(ƛ M) · M') | inj₁ (V-ƛ M) | inj₁ VM' =
  inj₂ (_ ,, ([] ,, (ƛ M · M' ,, ((inj₁ (M [ M' ] ,, β-ƛ VM')) ,, refl))))
lemma51 (M · M') | inj₁ (V-I⇒ b p q r σ base x refl .M X) | inj₁ VM' =
  inj₂ (_ ,, [] ,, M · M' ,, inj₁ (_ ,, (β-sbuiltin b σ p q _ r M (deval VM') x VM')) ,, refl)
lemma51 (M · M') | inj₁ V@(V-I⇒ b p q r σ (skip⋆ p₁) x refl .M X) | inj₁ VM' =
  inj₁ (V-IΠ b p q r σ p₁ (x ,, M' ,, VM') refl (M · M') (step X V VM'))
lemma51 (M · M') | inj₁ V@(V-I⇒ b p q r σ (skip p₁) x refl .M X) | inj₁ VM' =
  inj₁ (V-I⇒ b p q r σ p₁ (x ,, M' ,, VM') refl (M · M') (step X V VM'))
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, VM ·r E ,, L ,, p ,, cong (M ·_) q)
lemma51 (Λ M) = inj₁ (V-Λ M)
lemma51 (M ·⋆ A) with lemma51 M
... | inj₂ (B ,, E ,, L ,, p ,, p') = inj₂ (B ,, E ·⋆ A ,, L ,, p ,, cong (_·⋆ A) p')
... | inj₁ (V-Λ M') =
  inj₂ (_ ,, [] ,, M ·⋆ A ,, inj₁ (M' [ A ]⋆ ,, β-Λ) ,, refl)
... | inj₁ (V-IΠ b p q r σ base x refl .M X) =
  inj₂ (_ ,, [] ,, M ·⋆ A ,, inj₁ (_ ,, β-sbuiltin⋆ b σ p q _ r M x) ,, refl)
... | inj₁ V@(V-IΠ b {C = C} p q r σ (skip⋆ p₁) x refl .M X) =
  inj₁ (convValue (Πlem p₁ A C σ) (V-IΠ b {C = C} p q r (subNf-cons σ A) p₁ (x ,, A) refl (conv⊢ refl (Πlem p₁ A C σ) (M ·⋆ A)) (convBV _ (step⋆ X V))))
... | inj₁ V@(V-IΠ b {C = C} p q r σ (skip p₁) x refl .M X) =
  inj₁ (convValue (⇒lem p₁ σ C) (V-I⇒ b p q r (subNf-cons σ A) p₁ (x ,, A) refl (conv⊢ refl (⇒lem p₁ σ C) (M ·⋆ A)) (convBV _ (step⋆ X V))))
lemma51 (wrap A B M) with lemma51 M
... | inj₁ V = inj₁ (V-wrap V)
... | inj₂ (C ,, E ,, L ,, p ,, p') =
  inj₂ (C ,, wrap E ,, L ,, p ,, cong (wrap A B) p')
lemma51 (unwrap M) with lemma51 M
... | inj₁ (V-wrap V) = inj₂ (_ ,, [] ,, unwrap M ,, inj₁ (deval V ,, β-wrap V) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, p') =
  inj₂ (B ,, unwrap E ,, L ,, p ,, cong unwrap p')
lemma51 (con c) = inj₁ (V-con c)
lemma51 (ibuiltin b) = inj₁ (ival b)
lemma51 (error _) = inj₂ (_ ,, ([] ,, (error _ ,, (inj₂ E-error) ,, refl)))

progress' : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, refl) = step (ruleEC E p refl refl)
... | inj₂ (B ,, E ,, L ,, inj₂ E-error ,, refl) = step (ruleErr E)

data EProgress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{B}(E : EC A B){L L' : ∅ ⊢ B}
    → L —→⋆ L'
    → M ≡ E [ L ]ᴱ
      -------------
    → EProgress M
  done :
      Value M
      ----------
    → EProgress M

  error : ∀{B}(E : EC A B){L : ∅ ⊢ B}
    →  Error L
    →  M ≡ E [ L ]ᴱ
      -------
    → EProgress M

lemma51' : ∀{A}(M : ∅ ⊢ A) → EProgress M
lemma51' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, p') = step E p p'
... | inj₂ (B ,, E ,, L ,, inj₂ e ,, p) = error E e p
