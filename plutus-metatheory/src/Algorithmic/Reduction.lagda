\begin{code}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
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
\end{code}

## Values

\begin{code}

ITel : Builtin → ∀{Φ} → Ctx Φ → SubNf Φ ∅ → Set
data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set where

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
    → (t : ∅ ⊢ substNf σ (<C'2type (skip p) C))
    → Value t

  V-IΠ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{K}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅) -- could try one at a time
      (p : (Δ ,⋆ K) ≤C' Γ)
    → ITel b Δ σ
    → (t : ∅ ⊢ substNf σ (<C'2type (skip⋆ p) C))
    → Value t

ITel b ∅       σ = ⊤
ITel b (Γ ,⋆ J) σ = ITel b Γ (σ ∘ S) × ∅ ⊢Nf⋆ J
ITel b (Γ , A) σ = ITel b Γ σ × Σ (∅ ⊢ substNf σ A) Value

deval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢ A
deval {u = u} _ = u
tval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢Nf⋆ *
tval {A = A} _ = A
\end{code}

\begin{code}
voidVal : Value (con unit)
voidVal = V-con unit
\end{code}

\begin{code}
data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
\end{code}

\begin{code}
convVal :  ∀ {A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → Value t → Value (conv⊢ refl q t)
convVal refl v = v
\end{code}

\begin{code}
IBUILTIN : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      (σ : SubNf Φ ∅)
    → (tel : ITel b Γ σ)
      -----------------------------
    → Σ (∅ ⊢ substNf σ C) λ t → Value t ⊎ Error t 
      -- ^ should be val or error to avoid throwing away work
IBUILTIN addInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i + j)))
IBUILTIN subtractInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i - j)))
IBUILTIN multiplyInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) = _ ,, inj₁ (V-con (integer (i ** j)))
IBUILTIN divideInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₂ E-error -- divide by zero
... | yes p = _ ,, inj₁ (V-con (integer (div i j)))
IBUILTIN quotientInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₂ E-error -- divide by zero
... | yes p = _ ,, inj₁ (V-con (integer (quot i j)))
IBUILTIN remainderInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₂ E-error -- divide by zero
... | yes p = _ ,, inj₁ (V-con (integer (rem i j)))
IBUILTIN modInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ ,, inj₂ E-error -- divide by zero
... | yes p = _ ,, inj₁ (V-con (integer (mod i j)))
IBUILTIN lessThanInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i <? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))

IBUILTIN lessThanEqualsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i ≤? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN greaterThanInteger σ  ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i Builtin.Constant.Type.>? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN greaterThanEqualsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j)) with i Builtin.Constant.Type.≥? j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN equalsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j))  with i ≟ j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN concatenate σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bytestring (concat b b')))
IBUILTIN takeByteString σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (take i b)))
IBUILTIN dropByteString σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (drop i b)))
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
    → Σ (∅ ⊢ substNf σ C') λ t → Value t ⊎ Error t
    
IBUILTIN' b refl refl σ tel _ refl = IBUILTIN b σ tel
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ξ-·₁ : {A B : ∅ ⊢Nf⋆ *} {L L′ : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : {A B : ∅ ⊢Nf⋆ *}{V : ∅ ⊢ A ⇒ B} {M M′ : ∅ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L L' : ∅ ⊢ Π B}{A}
    → L —→ L'
      -----------------
    → L ·⋆ A —→ L' ·⋆ A

  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A —→ N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) —→ M

  ξ-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ μ A B}
    → M —→ M'
    → unwrap M —→ unwrap M'
    
  ξ-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
    → M —→ M'
    → wrap A B M —→ wrap A B M'

  E-·₂ : {A B : ∅ ⊢Nf⋆ *} {L : ∅ ⊢ A ⇒ B}
    → Value L
    → L · error A —→ error B
  E-·₁ : {A B : ∅ ⊢Nf⋆ *}{M : ∅ ⊢ A}
    → error (A ⇒ B) · M —→ error B
  E-·⋆ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{A : ∅ ⊢Nf⋆ K}
    → error (Π B) ·⋆ A —→ error (B [ A ]Nf)
  E-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → unwrap (error (μ A B))
        —→ error (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  E-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → wrap A B (error _) —→ error (μ A B) 

  β-sbuiltin :
      (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢Nf⋆ *}
    → (σ : SubNf Φ' ∅)
    → (p : Φ ≡ Φ')
    → (q : substEq Ctx p Γ ≡  Γ' , A)
    → (C' : Φ' ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
    → (t : ∅ ⊢ substNf σ A ⇒ substNf σ C')
    → (u : ∅ ⊢ substNf σ A)
    → (tel : ITel b Γ' σ)
    → (v : Value u)
      -----------------------------
    → t · u —→ proj₁ (IBUILTIN' b p q σ (tel ,, u ,, v) C' r)

  β-sbuiltin⋆ :
      (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}{K}{A : ∅ ⊢Nf⋆ K}
    → (σ : SubNf Φ' ∅)
    → (p : Φ ≡ Φ' ,⋆ K)
    → (q : substEq Ctx p Γ ≡  (Γ' ,⋆ K))
    → (C' : Φ' ,⋆ K ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
    → (t : ∅ ⊢ substNf σ (Π C'))
    → (tel : ITel b Γ' σ)
      -----------------------------
    → t ·⋆ A —→ conv⊢ refl (substNf-cons-[]Nf C') (proj₁ (IBUILTIN' b p q (substNf-cons σ A) (tel ,, A) C' r))
\end{code}

\begin{code}
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


\end{code}

\begin{code}
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
\end{code}

\begin{code}
progress-·V :  {A B : ∅ ⊢Nf⋆ *}
  → {t : ∅ ⊢ A ⇒ B} → Value t
  → {u : ∅ ⊢ A} → Progress u
  → Progress (t · u)
progress-·V v       (step q)        = step (ξ-·₂ v q)
progress-·V v       (error E-error) = step (E-·₂ v)
progress-·V (V-ƛ t) (done w)        = step (β-ƛ w)
progress-·V (V-I⇒ b p q r σ base vs t) (done v) =
  step (β-sbuiltin b σ p q _ r t (deval v) vs v)
-- ^ we're done, call BUILTIN
progress-·V (V-I⇒ b p' q r σ (skip⋆ p) vs t) (done v) =
  done (V-IΠ b p' q r σ p (vs ,, deval v ,, v) (t · deval v))
progress-·V (V-I⇒ b p' q r σ (skip p)  vs t) (done v) =
  done (V-I⇒ b p' q r σ p (vs ,, deval v ,, v) (t · deval v))

progress-· :  {A B : ∅ ⊢Nf⋆ *}
  → {t : ∅ ⊢ A ⇒ B} → Progress t
  → {u : ∅ ⊢ A} → Progress u
  → Progress (t · u)
progress-· (step p)  q = step (ξ-·₁ p)
progress-· (done v)  q = progress-·V v q
progress-· (error E-error) q = step E-·₁

convValue : ∀{A A'}{t : ∅ ⊢ A}(p : A ≡ A') → Value (conv⊢ refl p t) → Value t
convValue refl v = v

ival : ∀ b → Value (ibuiltin b)
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
ival sha2-256 = V-I⇒ sha2-256 {Γ = proj₁ (proj₂ (ISIG sha2-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha2-256))} refl refl refl (λ()) base tt (ibuiltin sha2-256)
ival sha3-256 = V-I⇒ sha3-256 {Γ = proj₁ (proj₂ (ISIG sha3-256))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG sha3-256))} refl refl refl (λ()) base tt (ibuiltin sha3-256)
ival verifySignature = V-I⇒ verifySignature {Γ = proj₁ (proj₂ (ISIG verifySignature))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG verifySignature))} refl refl refl (λ()) (≤Cto≤C' (skip (skip base))) tt (ibuiltin verifySignature)
ival equalsByteString = V-I⇒ equalsByteString {Γ = proj₁ (proj₂ (ISIG equalsByteString))}{Δ = ∅}{C = proj₂ (proj₂ (ISIG equalsByteString))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin equalsByteString)
ival ifThenElse = V-IΠ ifThenElse {Γ = proj₁ (proj₂ (ISIG ifThenElse))}{C = proj₂ (proj₂ (ISIG ifThenElse))} refl refl refl (λ()) (≤Cto≤C' (skip (skip (skip base)))) tt (ibuiltin ifThenElse)
ival charToString = V-I⇒ charToString {Γ = proj₁ (proj₂ (ISIG charToString))}{C = proj₂ (proj₂ (ISIG charToString))} refl refl refl (λ()) base tt (ibuiltin charToString)
ival append = V-I⇒ append {Γ = proj₁ (proj₂ (ISIG append))}{C = proj₂ (proj₂ (ISIG append))} refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin append)
ival trace = V-I⇒ trace {Γ = proj₁ (proj₂ (ISIG trace))}{C = proj₂ (proj₂ (ISIG trace))} refl refl refl (λ()) base tt (ibuiltin trace)

progress-·⋆ : ∀{K B}{t : ∅ ⊢ Π B} → Progress t → (A : ∅ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)        A = step (ξ-·⋆ p)
progress-·⋆ (done (V-Λ t))  A = step β-Λ
progress-·⋆ (error E-error) A = step E-·⋆
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip⋆ p) vs t)) A = done (convValue (Πlem p A C σ) (V-IΠ b {C = C} p' q r (substNf-cons σ A) p (vs ,, A) (conv⊢ refl (Πlem p A C σ) (t ·⋆ A))) )
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip p) vs t))  A = done (convValue (⇒lem p σ C) (V-I⇒ b p' q r (substNf-cons σ A) p (vs ,, A) (conv⊢ refl (⇒lem p σ C) (t ·⋆ A) )))
progress-·⋆ (done (V-IΠ b p q r σ base vs t)) A = step (β-sbuiltin⋆ b σ p q _ r t vs)
-- ^ it's the last one, call BUILTIN

progress-unwrap : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ μ A B}
  → Progress t → Progress (unwrap t)
progress-unwrap (step q) = step (ξ-unwrap q)
progress-unwrap (done (V-wrap v)) = step (β-wrap v)
progress-unwrap {A = A} (error E-error) =
  step (E-unwrap {A = A})

progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
   → Progress M → Progress (wrap A B M)
progress-wrap (step p)        = step (ξ-wrap p)
progress-wrap (done v)        = done (V-wrap v)
progress-wrap (error E-error) = step E-wrap
progress (ƛ M)                = done (V-ƛ M)
progress (M · N)              = progress-· (progress M) (progress N)
progress (Λ M)                = done (V-Λ M)
progress (M ·⋆ A)             = progress-·⋆ (progress M) A
progress (wrap A B M) = progress-wrap (progress M)
progress (unwrap M)          = progress-unwrap (progress M)
progress (con c)              = done (V-con c)
progress (ibuiltin b) = done (ival b)
progress (error A)            = error E-error

open import Data.Nat
progressor : ℕ → ∀{A} → (t : ∅ ⊢ A) → Either RuntimeError (Maybe (∅ ⊢ A))
progressor zero t = inj₁ gasError
progressor (suc n) t with progress t
... | step {N = t'} _ = progressor n t'
... | done v = inj₂ (just (deval v))
... | error _ = inj₂ nothing -- should this be an runtime error?
--

open import Data.Empty

-- progress is disjoint:

{-
-- a value cannot make progress
val-red : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → Value t → ¬ (Σ (∅ ⊢ σ) (t —→_))
val-red (V-wrap p) (.(wrap _ _ _) ,, ξ-wrap q) = val-red p (_ ,, q)
val-red (V-wrap v) (.(error (μ _ _)) ,, E-wrap) = {!val-err v!}

val-red (V-I⇒ b p₁ q r σ p' x t) (t' ,, p) = {!!}
-- this is impossible because p' : Δ , A ≤C' Γ and we can only compute
-- if we have a full telescope...  but, t can be anything here,
-- perhaps it's better to match on the rules instead?
val-red (V-IΠ b p₁ q r σ p₂ x _) (t ,, p) = {!!}

valT-redT : ∀ {Δ}{σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel ∅ Δ σ As} → VTel Δ σ As ts → ¬ Σ (Tel ∅ Δ σ As) (ts —→T_)
valT-redT (v ,, vs) (.(_ ∷ _) ,, here p)    = val-red v (_ ,, p)
valT-redT (v ,, vs) (.(_ ∷ _) ,, there w p) = valT-redT vs (_ ,, p)

-- a value cannot be an error
val-err : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → Value t → ¬ (Error t)
val-err p E-error = {!!}

valT-errT : ∀ {Δ}{σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel ∅ Δ σ As} → VTel Δ σ As ts → ¬ (Any Error ts)
valT-errT (v ,, vs) (here p)    = val-err v p
valT-errT (v ,, vs) (there w p) = valT-errT vs p

-- an error cannot make progress
red-err : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → Σ (∅ ⊢ σ) (t —→_) → ¬ (Error t)
red-err () E-error

redT-errT : ∀ {Δ}{σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel ∅ Δ σ As} → Σ (Tel ∅ Δ σ As) (ts —→T_) → ¬ (Any Error ts)
redT-errT (.(_ ∷ _) ,, here p)    (here q)    = red-err (_ ,, p) q
redT-errT (.(_ ∷ _) ,, there v p) (here q)    = val-err v q
redT-errT (.(_ ∷ _) ,, here p)    (there w q) = val-red w (_ ,, p)
redT-errT (.(_ ∷ _) ,, there v p) (there w q) = redT-errT (_ ,, p) q

-- values are unique for a term
valUniq : ∀ {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) → (v v' : Value t) → v ≡ v'
valUniq .(ƛ _)         (V-ƛ _)    (V-ƛ _)     = refl
valUniq .(Λ _)         (V-Λ _)    (V-Λ _)     = refl
valUniq .(wrap _ _ _) (V-wrap v) (V-wrap v') = cong V-wrap (valUniq _ v v')
valUniq .(con cn)      (V-con cn) (V-con .cn) = refl
--valUniq _ (V-pbuiltin⋆ _ _ _ _) (V-pbuiltin⋆ _ _ _ _) = refl
--valUniq _ (V-pbuiltin _ _ _ _ _ _ ) (V-pbuiltin _ _ _ _ _ _ ) = refl
valUniq _ _ _ = {!!}

-- telescopes of values are unique for that telescope
vTelUniq : ∀ Δ → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → (tel : Tel ∅ Δ σ As)
  → (vtel vtel' : VTel Δ σ As tel)
  → vtel ≡ vtel'
<<<<<<< HEAD
vTelUniq Δ σ [] [] vtel vtel' = refl
vTelUniq Δ σ (A ∷ As) (t ∷ tel) (v ,, vtel) (v' ,, vtel') =
  cong₂ _,,_ (valUniq t v v') (vTelUniq Δ σ As tel vtel vtel') 
=======
vTelUniq Γ Δ σ [] [] vtel vtel' = refl
vTelUniq Γ Δ σ (A ∷ As) (t ∷ tel) (v ,, vtel) (v' ,, vtel') =
  cong₂ _,,_ (valUniq t v v') (vTelUniq Γ Δ σ As tel vtel vtel')
>>>>>>> 3d0fa53911081de50fa6a795563663300ddc8952

-- exclusive or
_xor_ : Set → Set → Set
A xor B = (A ⊎ B) × ¬ (A × B)

infixr 2 _xor_

-- a term cannot make progress and be a value

notboth : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → ¬ (Value t × Σ (∅ ⊢ σ) (t —→_))
notboth (v ,, p) = val-red v p

-- term cannot make progress and be error

notboth' : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → ¬ (Σ (∅ ⊢ σ) (t —→_) × Error t)
notboth' (p ,, e) = red-err p e

-- armed with this, we can upgrade progress to an xor

progress-xor : {σ : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ σ)
  → Value t xor (Σ (∅ ⊢ σ) (t —→_)) xor Error t
progress-xor t with progress t
progress-xor t | step p  = (inj₂ ((inj₁ (_ ,, p)) ,, λ{(p ,, e) → red-err p e})) ,, λ { (v ,, inj₁ p ,, q) → val-red v p ; (v ,, inj₂ e ,, q) → val-err v e}
progress-xor t | done v  = (inj₁ v) ,, (λ { (v' ,, inj₁ p ,, q) → val-red v p ; (v' ,, inj₂ e ,, q) → val-err v e})
progress-xor t | error e = (inj₂ ((inj₂ e) ,, (λ { (p ,, e) → red-err p e}))) ,, λ { (v ,, q) → val-err v e }
-- the reduction rules are deterministic
det : ∀{σ : ∅ ⊢Nf⋆ *}{t t' t'' : ∅ ⊢ σ}
  → (p : t —→ t')(q : t —→ t'') → t' ≡ t''
detT : ∀{Δ}{σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}{As}{ts ts' ts'' : Tel ∅ Δ σ As}
    → (p : ts —→T ts')(q : ts —→T ts'') → ts' ≡ ts''

det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ w q) = ⊥-elim (val-red w (_ ,, p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (val-red v (_ ,, q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (val-red w (_ ,, p))
det (ξ-·⋆ p) (ξ-·⋆ q) = cong (_·⋆ _) (det p q)
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (val-red v (_ ,, q))
det (β-ƛ v) (β-ƛ w) = refl
det β-Λ β-Λ = refl
det (β-wrap p) (β-wrap q) = refl
det (β-wrap p) (ξ-unwrap q) = ⊥-elim (val-red (V-wrap p) (_ ,, q))
det (ξ-unwrap p) (β-wrap q) = ⊥-elim (val-red (V-wrap q) (_ ,, p))
det (ξ-unwrap p) (ξ-unwrap q) = cong unwrap (det p q)
det (ξ-wrap p) (ξ-wrap q) = cong (wrap _ _) (det p q)
det (β-builtin bn σ ts vs) (β-builtin .bn .σ .ts ws) =
  cong (BUILTIN bn σ ts) (vTelUniq _ σ _ ts vs ws)
det (β-builtin bn σ ts vs) (ξ-builtin .bn .σ p) =
  ⊥-elim (valT-redT vs (_ ,, p))
det (ξ-builtin bn σ p) (β-builtin .bn .σ ts vs) =
  ⊥-elim (valT-redT vs (_ ,, p))
det (ξ-builtin bn σ p) (ξ-builtin .bn .σ p') = cong (builtin bn σ) (detT p p')
det (β-builtin _ _ _ vs) (E-builtin _ _ _ p) = ⊥-elim (valT-errT vs p)
det (ξ-builtin _ _ p) (E-builtin _ _ _ q) = ⊥-elim (redT-errT (_ ,, p) q)
det (E-builtin _ _ _ _) (E-builtin _ _ _ _) = refl
det (E-builtin bn σ ts p) (β-builtin .bn .σ .ts vs) = ⊥-elim (valT-errT vs p)
det (E-builtin bn σ ts p) (ξ-builtin .bn .σ q) = ⊥-elim (redT-errT (_ ,, q) p)
det E-·₁ (ξ-·₁ p) = {!!}
det (E-·₂ v) (ξ-·₁ p) = ⊥-elim (val-red v (_ ,, p))
det (E-·₂ v) (E-·₂ w) = refl
det (E-·₂ p) E-·₁ = {!!}
det (ξ-·₁ p) (E-·₂ v) = ⊥-elim (val-red v (_ ,, p))
det E-·₁ (E-·₂ p) = {!!}
det E-·₁ E-·₁ = refl
det E-·⋆ E-·⋆ = refl
det E-unwrap E-unwrap = refl
det E-wrap E-wrap = refl
det _ _ = {!!}

detT (here p)    (there w q) = ⊥-elim (val-red w (_ ,, p))
detT (there v p) (here q)    = ⊥-elim (val-red v (_ ,, q))
detT (there v p) (there w q) = cong (_ ∷_) (detT p q)
detT (here p) (here q) = cong (_∷ _) (det p q)
-}

