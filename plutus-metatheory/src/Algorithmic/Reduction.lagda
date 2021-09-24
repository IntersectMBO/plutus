\begin{code}
{-# OPTIONS --rewriting #-}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
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

open import Utils hiding (TermCon)
open import Type
import Type.RenamingSubstitution as T
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Maybe using (just;from-just)
open import Data.String using (String)
open import Algorithmic
\end{code}

## Values

\begin{code}
data _≤C_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → Γ ≤C Γ' → Γ ≤C (Γ' ,⋆ K)
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢Nf⋆ *} → Γ ≤C Γ' → Γ ≤C (Γ' , A)

data _≤C'_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C' Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → (Γ ,⋆ K) ≤C' Γ' → Γ ≤C' Γ'
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ ⊢Nf⋆ *} → (Γ , A) ≤C' Γ' → Γ ≤C' Γ'

skip' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{A} → Γ ≤C' Γ' → Γ ≤C' (Γ' , A)
skip' base = skip base
skip' (skip⋆ p) = skip⋆ (skip' p)
skip' (skip p) = skip (skip' p)

skip⋆' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{K} → Γ ≤C' Γ' → Γ ≤C' (Γ' ,⋆ K)
skip⋆' base = skip⋆ base
skip⋆' (skip⋆ p) = skip⋆ (skip⋆' p)
skip⋆' (skip p) = skip (skip⋆' p)

≤Cto≤C' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'} → Γ ≤C Γ' → Γ ≤C' Γ'
≤Cto≤C' base      = base
≤Cto≤C' (skip⋆ p) = skip⋆' (≤Cto≤C' p)
≤Cto≤C' (skip p)  = skip' (≤Cto≤C' p)

<C'2type : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'} → Γ ≤C' Γ' → Φ' ⊢Nf⋆ * → Φ ⊢Nf⋆ *
<C'2type base      C = C
<C'2type (skip⋆ p) C = Π (<C'2type p C)
<C'2type (skip {A = A} p)  C = A ⇒ <C'2type p C

Πlem : ∀{K K'}{Φ Φ'}{Δ : Ctx Φ'}{Γ : Ctx Φ}(p : ((Δ ,⋆ K) ,⋆ K') ≤C' Γ)
  (A : ∅ ⊢Nf⋆ K)(C : Φ ⊢Nf⋆ *)(σ : SubNf Φ' ∅)
  → (Π
       (eval
        (T.sub (T.exts (T.exts (λ x → embNf (σ x))))
         (embNf (<C'2type p C)))
        (exte (exte (idEnv ∅))))
       [ A ]Nf)
      ≡ subNf (subNf-cons σ A) (Π (<C'2type p C))
Πlem p A C σ = sym (subNf-cons-[]Nf (Π (<C'2type p C)))

⇒lem : ∀{K}{A : ∅ ⊢Nf⋆ K}{Φ Φ'}{Δ : Ctx Φ'}{Γ : Ctx Φ}{B : Φ' ,⋆ K ⊢Nf⋆ *}
       (p : ((Δ ,⋆ K) , B) ≤C' Γ)(σ : SubNf Φ' ∅)(C : Φ ⊢Nf⋆ *)
  → ((eval (T.sub (T.exts (λ x → embNf (σ x))) (embNf B))
        (exte (idEnv ∅))
        ⇒
        eval (T.sub (T.exts (λ x → embNf (σ x))) (embNf (<C'2type p C)))
        (exte (idEnv ∅)))
       [ A ]Nf)
      ≡ subNf (subNf-cons σ A) (B ⇒ <C'2type p C)
⇒lem {B = B} p σ C = sym (subNf-cons-[]Nf (B ⇒ <C'2type p C)) 

-- something very much like a substitution
-- labelled by a builtin and given a first order presentation
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

  V-con : ∀{tcn : TyCon _}
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
    → (t : ∅ ⊢ subNf σ (<C'2type (skip p) C))
    → Value t

  V-IΠ : ∀(b : Builtin){Φ Φ'}{Γ : Ctx Φ}{Δ : Ctx Φ'}{K}{C : Φ ⊢Nf⋆ *}
    → let Ψ ,, Γ' ,, C' = ISIG b in
      (p : Ψ ≡ Φ)
    → (q : substEq Ctx p Γ' ≡ Γ)
    → (r : substEq (_⊢Nf⋆ *) p C' ≡ C)
    → (σ : SubNf Φ' ∅) -- could try one at a time
      (p : (Δ ,⋆ K) ≤C' Γ)
    → ITel b Δ σ
    → (t : ∅ ⊢ subNf σ (<C'2type (skip⋆ p) C))
    → Value t

ITel b ∅       σ = ⊤
ITel b (Γ ,⋆ J) σ = ITel b Γ (σ ∘ S) × ∅ ⊢Nf⋆ J
ITel b (Γ , A) σ = ITel b Γ σ × Σ (∅ ⊢ subNf σ A) Value

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
IBUILTIN equalsInteger σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (integer j))  with i ≟ j
... | no ¬p = _ ,, inj₁ (V-con (bool false))
... | yes p = _ ,, inj₁ (V-con (bool true))
IBUILTIN appendByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bytestring (concat b b')))
IBUILTIN consByteString σ ((tt ,, _ ,, V-con (integer i)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (cons i b)))
IBUILTIN sliceByteString σ (((tt ,, _ ,, V-con (integer st)) ,, _ ,, V-con (integer n)) ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (slice st n b)))
IBUILTIN lengthOfByteString σ (tt ,, _ ,, V-con (bytestring b)) =
  _ ,, inj₁ (V-con (integer (length b)))
IBUILTIN indexByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (integer i)) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = _ ,, inj₂ E-error
... | yes _ with i <? length b
... | no _ =  _ ,, inj₂ E-error
... | yes _ = _ ,, inj₁ (V-con (integer (index b i)))
IBUILTIN equalsByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (equals b b')))
IBUILTIN lessThanByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (B< b b')))
IBUILTIN lessThanEqualsByteString σ ((tt ,, _ ,, V-con (bytestring b)) ,, _ ,, V-con (bytestring b')) = _ ,, inj₁ (V-con (bool (B> b b')))
IBUILTIN sha2-256 σ (tt ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (SHA2-256 b)))
IBUILTIN sha3-256 σ (tt ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (SHA3-256 b)))
IBUILTIN blake2b-256 σ (tt ,, _ ,, V-con (bytestring b)) = _ ,, inj₁ (V-con (bytestring (BLAKE2B-256 b)))
IBUILTIN verifySignature σ (((tt ,, _ ,, V-con (bytestring k)) ,, _ ,, V-con (bytestring d)) ,, _ ,, V-con (bytestring c)) with verifySig k d c
... | just b = _ ,, inj₁ (V-con (bool b))
... | nothing = _ ,, inj₂ E-error -- not sure what this is for
IBUILTIN appendString σ ((tt ,, _ ,, V-con (string s)) ,, _ ,, V-con (string s')) =
  _ ,, inj₁ (V-con (string (primStringAppend s s')))
IBUILTIN equalsString σ ((tt ,, _ ,, V-con (string s)) ,, _ ,, V-con (string s')) = _ ,, inj₁ (V-con (bool (primStringEquality s s')))
IBUILTIN encodeUtf8 σ (tt ,, _ ,, V-con (string s)) =
  _ ,, inj₁ (V-con (bytestring (ENCODEUTF8 s)))
IBUILTIN decodeUtf8 σ (tt ,, _ ,, V-con (bytestring b)) with DECODEUTF8 b
... | nothing = _ ,, inj₂ E-error
... | just s  = _ ,, inj₁ (V-con (string s))
IBUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, V-con (bool false)) ,, t) ,, f) =
  _ ,, inj₁ (proj₂ f)
IBUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, V-con (bool true)) ,, t) ,, f) =
  _ ,, inj₁ (proj₂ t)
IBUILTIN trace σ (((tt ,, _) ,, _ ,, V-con (string s)) ,, v) =
  _ ,, inj₁ (TRACE s (proj₂ v))
IBUILTIN iData σ (tt ,, _ ,, V-con (integer i)) =
  _ ,, inj₁ (V-con (Data (iDATA i)))
IBUILTIN bData σ (tt ,, _ ,, V-con (bytestring b)) =
  _ ,, inj₁ (V-con (Data (bDATA b)))
IBUILTIN unIData σ (tt ,, _ ,, V-con (Data (iDATA i))) =
  _ ,, inj₁ (V-con (integer i))
IBUILTIN unBData σ (tt ,, _ ,, V-con (Data (bDATA b))) =
  _ ,, inj₁ (V-con (bytestring b))
IBUILTIN b σ t = _ ,, inj₂ E-error

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
    → (t : ∅ ⊢ subNf σ A ⇒ subNf σ C')
    → (u : ∅ ⊢ subNf σ A)
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
    → (t : ∅ ⊢ subNf σ (Π C'))
    → (tel : ITel b Γ' σ)
      -----------------------------
    → t ·⋆ A —→ conv⊢ refl (subNf-cons-[]Nf C') (proj₁ (IBUILTIN' b p q (subNf-cons σ A) (tel ,, A) C' r))
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
ival addInteger = V-I⇒ addInteger refl refl refl (λ()) (skip base) tt (ibuiltin addInteger)
ival subtractInteger = V-I⇒ subtractInteger refl refl refl (λ()) (skip base) tt (ibuiltin subtractInteger)
ival multiplyInteger = V-I⇒ multiplyInteger refl refl refl (λ()) (skip base) tt (ibuiltin multiplyInteger)
ival divideInteger = V-I⇒ divideInteger refl refl refl (λ()) (skip base) tt (ibuiltin divideInteger)
ival quotientInteger = V-I⇒ quotientInteger refl refl refl (λ()) (skip base) tt (ibuiltin quotientInteger)
ival remainderInteger = V-I⇒ remainderInteger refl refl refl (λ()) (skip base) tt (ibuiltin remainderInteger)
ival modInteger = V-I⇒ modInteger refl refl refl (λ()) (skip base) tt (ibuiltin modInteger)
ival lessThanInteger = V-I⇒ lessThanInteger refl refl refl (λ()) (skip base) tt (ibuiltin lessThanInteger)
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin lessThanEqualsInteger)
ival equalsInteger = V-I⇒ equalsInteger refl refl refl (λ()) (skip base) tt (ibuiltin equalsInteger)
ival lessThanByteString = V-I⇒ lessThanByteString refl refl refl (λ()) (skip base) tt (ibuiltin lessThanByteString)
ival lessThanEqualsByteString = V-I⇒ lessThanEqualsByteString refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (ibuiltin lessThanEqualsByteString)
ival sha2-256 = V-I⇒ sha2-256 refl refl refl (λ()) base tt (ibuiltin sha2-256)
ival sha3-256 = V-I⇒ sha3-256 refl refl refl (λ()) base tt (ibuiltin sha3-256)
ival verifySignature = V-I⇒ verifySignature refl refl refl (λ()) (skip (skip base)) tt (ibuiltin verifySignature)
ival equalsByteString = V-I⇒ equalsByteString refl refl refl (λ()) (skip base) tt (ibuiltin equalsByteString)
ival appendByteString = V-I⇒ appendByteString refl refl refl (λ()) (skip base) tt (ibuiltin appendByteString)
ival appendString = V-I⇒ appendString refl refl refl (λ()) (skip base) tt (ibuiltin appendString)
ival ifThenElse = V-IΠ ifThenElse refl refl refl (λ()) (skip (skip (skip base))) tt (ibuiltin ifThenElse)
ival trace = V-IΠ trace refl refl refl (λ()) (skip (skip base)) tt (ibuiltin trace)
ival equalsString = V-I⇒ equalsString refl refl refl (λ()) (skip base) tt (ibuiltin equalsString)
ival encodeUtf8 = V-I⇒ encodeUtf8 refl refl refl (λ()) base tt (ibuiltin encodeUtf8)
ival decodeUtf8 = V-I⇒ decodeUtf8 refl refl refl (λ()) base tt (ibuiltin decodeUtf8)
ival fstPair = V-IΠ fstPair refl refl refl (λ()) (skip⋆ (skip base)) tt (ibuiltin fstPair)
ival sndPair = V-IΠ sndPair refl refl refl (λ()) (skip⋆ (skip base)) tt (ibuiltin sndPair)
ival nullList = V-IΠ nullList refl refl refl (λ()) (skip base) tt (ibuiltin nullList)
ival headList = V-IΠ headList refl refl refl (λ()) (skip base) tt (ibuiltin headList)
ival tailList = V-IΠ tailList refl refl refl (λ()) (skip base) tt (ibuiltin tailList)
ival chooseList = V-IΠ chooseList refl refl refl (λ()) (skip⋆ (skip (skip (skip base)))) tt (ibuiltin chooseList)
ival constrData = V-I⇒ constrData refl refl refl (λ()) (skip base) tt (ibuiltin constrData)
ival mapData = V-I⇒ mapData refl refl refl (λ()) base tt (ibuiltin mapData)
ival listData = V-I⇒ listData refl refl refl (λ()) base tt (ibuiltin listData)
ival iData = V-I⇒ iData refl refl refl (λ()) base tt (ibuiltin iData)
ival bData = V-I⇒ bData refl refl refl (λ()) base tt (ibuiltin bData)
ival unConstrData = V-I⇒ unConstrData refl refl refl (λ()) base tt (ibuiltin unConstrData)
ival unMapData = V-I⇒ unMapData refl refl refl (λ()) base tt (ibuiltin unMapData) 
ival unListData = V-I⇒ unListData refl refl refl (λ()) base tt (ibuiltin unListData)
ival unIData = V-I⇒ unIData refl refl refl (λ()) base tt (ibuiltin unIData)
ival unBData = V-I⇒ unBData refl refl refl (λ()) base tt (ibuiltin unBData)
ival equalsData = V-I⇒ equalsData refl refl refl (λ()) (skip base) tt (ibuiltin equalsData)
ival chooseData = V-IΠ chooseData refl refl refl (λ()) (skip (skip (skip (skip (skip (skip base)))))) tt (ibuiltin chooseData)
ival chooseUnit = V-IΠ chooseUnit refl refl refl (λ()) (skip (skip base)) tt (ibuiltin chooseUnit)
ival mkPairData = V-I⇒ mkPairData refl refl refl (λ()) (skip base) tt (ibuiltin mkPairData)
ival mkNilData = V-I⇒ mkNilData refl refl refl (λ()) base tt (ibuiltin mkNilData)
ival mkNilPairData = V-I⇒ mkNilPairData refl refl refl (λ()) base tt (ibuiltin mkNilPairData)
ival mkCons = V-I⇒ mkCons refl refl refl (λ()) (skip base) tt (ibuiltin mkCons)
ival consByteString = V-I⇒ consByteString refl refl refl (λ()) (skip base) tt (ibuiltin consByteString)
ival sliceByteString = V-I⇒ sliceByteString refl refl refl (λ()) (skip (skip base)) tt (ibuiltin sliceByteString)
ival lengthOfByteString = V-I⇒ lengthOfByteString refl refl refl (λ()) base tt (ibuiltin lengthOfByteString)
ival indexByteString = V-I⇒ indexByteString refl refl refl (λ()) (skip base) tt (ibuiltin indexByteString)
ival blake2b-256 = V-I⇒ blake2b-256 refl refl refl (λ()) base tt (ibuiltin blake2b-256)

progress-·⋆ : ∀{K B}{t : ∅ ⊢ Π B} → Progress t → (A : ∅ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)        A = step (ξ-·⋆ p)
progress-·⋆ (done (V-Λ t))  A = step β-Λ
progress-·⋆ (error E-error) A = step E-·⋆
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip⋆ p) vs t)) A = done (convValue (Πlem p A C σ) (V-IΠ b {C = C} p' q r (subNf-cons σ A) p (vs ,, A) (conv⊢ refl (Πlem p A C σ) (t ·⋆ A))) )
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip p) vs t))  A = done (convValue (⇒lem p σ C) (V-I⇒ b p' q r (subNf-cons σ A) p (vs ,, A) (conv⊢ refl (⇒lem p σ C) (t ·⋆ A) )))
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
