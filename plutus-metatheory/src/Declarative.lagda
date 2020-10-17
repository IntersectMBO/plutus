\begin{code}
module Declarative where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality
open import Builtin

-- these things should perhaps be rexported...
open import Builtin.Constant.Type
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con

open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.Int
open import Data.Integer renaming (_*_ to _**_)
open import Data.Empty
open import Data.Product hiding (_,_)
open import Relation.Binary hiding (_⇒_)
import Data.Nat as ℕ
open import Data.Unit hiding (_≤_)
open import Data.Vec hiding ([_]; take; drop)
open import Data.List hiding ([_]; length; take; drop)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat hiding (_^_; _≤_; _<_; _>_; _≥_)
open import Function hiding (_∋_)
import Data.Bool as Bool
open import Data.String
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_
\end{code}

## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
--data Ctx : Set
--∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx : Ctx⋆ → Set where
  ∅ : Ctx ∅
  _,⋆_ : ∀{Γ⋆} → Ctx Γ⋆ → (J : Kind) → Ctx (Γ⋆ ,⋆ J)
  _,_ : ∀{Γ⋆}(Γ : Ctx Γ⋆) → Γ⋆ ⊢⋆ * → Ctx Γ⋆
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
--∥ ∅ ∥       =  ∅
--∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
--∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type. Notice there is only
one Z as a type variable cannot be a term.
\begin{code}
data _∋_ : ∀{Γ⋆}(Γ : Ctx Γ⋆) → Γ⋆ ⊢⋆ * → Set where
  Z : ∀ {Φ Γ}{A : Φ ⊢⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Φ Γ} {A B : Φ ⊢⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K} {A : Φ ⊢⋆ *}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.

\begin{code}
data Tel {Φ} Γ Δ (σ : Sub Δ Φ) : List (Δ ⊢⋆ *) → Set

-- this is just a synonym for a substitution
ITel : ∀ {Φ}{Ψ} Γ Δ → Sub Φ Ψ → Set

data _≤L_ {A : Set} : List A → List A → Set where
 base : ∀{as} → as ≤L as
 skip : ∀{as as' a} → as ≤L as' → as ≤L (a ∷ as')

[]≤L : {A : Set}(as : List A) → [] ≤L as
[]≤L []       = base
[]≤L (a ∷ as) = skip ([]≤L as)

data _≤C⋆_ : Ctx⋆ → Ctx⋆ → Set where
 base : ∀{Φ} → Φ ≤C⋆ Φ
 skip : ∀{Φ Φ' K} → Φ ≤C⋆ Φ' → Φ ≤C⋆ (Φ' ,⋆ K)

data _≤C_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → Γ ≤C Γ' → Γ ≤C (Γ' ,⋆ K)
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢⋆ *} → Γ ≤C Γ' → Γ ≤C (Γ' , A)
 


ISIG : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢⋆ *
ISIG addInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG subtractInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG multiplyInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG divideInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG quotientInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG remainderInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG modInteger = _ ,, (∅ , con integer , con integer) ,, con integer
ISIG lessThanInteger = _ ,, (∅ , con integer , con integer) ,, con bool
ISIG lessThanEqualsInteger = _ ,, (∅ , con integer , con integer) ,, con bool
ISIG greaterThanInteger = _ ,, (∅ , con integer , con integer) ,, con bool
ISIG greaterThanEqualsInteger = _ ,, (∅ , con integer , con integer) ,, con bool
ISIG equalsInteger = _ ,, (∅ , con integer , con integer) ,, con bool
ISIG concatenate = _ ,, (∅ , con bytestring , con bytestring) ,, con bytestring
ISIG takeByteString = _ ,, (∅ , con bytestring , con integer) ,, con bytestring
ISIG dropByteString = _ ,, (∅ , con bytestring , con integer) ,, con bytestring
ISIG sha2-256 = _ ,, (∅ , con bytestring) ,, con bytestring
ISIG sha3-256 = _ ,, (∅ , con bytestring) ,, con bytestring
ISIG verifySignature = _ ,, (∅ , con bytestring , con bytestring , con bytestring) ,, con bool
ISIG equalsByteString = _ ,, (∅ , con bytestring , con bytestring) ,, con bool
ISIG ifThenElse = _ ,, (∅ , con bool ,⋆ * , ` Z , ` Z) ,, ` Z

sig2type : ∀ {Φ} → Ctx Φ → Φ ⊢⋆ * → ∅ ⊢⋆ *
sig2type ∅        C = C
sig2type (Γ ,⋆ J) C = sig2type Γ (Π C) 
sig2type (Γ , A)  C = sig2type Γ (A ⇒ C)

abstract2 : ∀ Ψ (As : List (Ψ ⊢⋆ *))(As' : List (Ψ ⊢⋆ *))(p : As' ≤L As)(C : Ψ ⊢⋆ *) → Ψ ⊢⋆ *
abstract2 Ψ As       .As base     C = C
abstract2 Ψ (A ∷ As) As' (skip p) C = abstract2 Ψ As As' p (A ⇒ C)

abstract1 : ∀ Ψ Ψ' (p : Ψ' ≤C⋆ Ψ)(C : Ψ ⊢⋆ *) → Ψ' ⊢⋆ *
abstract1 Ψ        Ψ  base     C = C
abstract1 (Ψ ,⋆ _) Ψ' (skip p) C = abstract1 Ψ Ψ' p (Π C)

open import Data.Sum

abstract3 : ∀ Φ Ψ Ψ' → (As : List (Ψ ⊢⋆ *))(As' : List (Ψ' ⊢⋆ *)) → (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L substEq (λ Φ → List (Φ ⊢⋆ *)) (sym p) As) → Ψ ⊢⋆ * → (Sub Ψ' Φ) → Φ ⊢⋆ *
abstract3 Φ Ψ Ψ As As' (inj₂ (refl ,, p)) C σ = subst σ (abstract2 Ψ As As' p C)
abstract3 Φ Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ =
  subst σ (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C)) 

abstract3-ren : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢⋆ *))(As' : List (Ψ' ⊢⋆ *)) → (p : (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L substEq (λ Φ → List (Φ ⊢⋆ *)) (sym p) As)) → (C : Ψ ⊢⋆ *) → (σ : Sub Ψ' Φ) → (ρ⋆ : Ren Φ Φ') →
  abstract3 Φ' Ψ Ψ' As As' p
  C (λ x → ren ρ⋆ (σ x)) 
  ≡
  ren ρ⋆
  (abstract3 Φ Ψ Ψ' As As' p
   C σ)
abstract3-ren Φ Φ' Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ ρ⋆ =
  ren-subst (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C))
abstract3-ren Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, p)) C σ ρ⋆ =
  ren-subst (abstract2 Ψ As As' p C)

abstract3-subst : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢⋆ *))(As' : List (Ψ' ⊢⋆ *)) → (p : (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L substEq (λ Φ → List (Φ ⊢⋆ *)) (sym p) As)) → (C : Ψ ⊢⋆ *) → (σ : Sub Ψ' Φ) → (ρ⋆ : Sub Φ Φ') →
  abstract3 Φ' Ψ Ψ' As As' p
  C (λ x → subst ρ⋆ (σ x)) 
  ≡
  subst ρ⋆
  (abstract3 Φ Ψ Ψ' As As' p
   C σ)
abstract3-subst Φ Φ' Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ ρ⋆ =
  subst-comp (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C))
abstract3-subst Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, p)) C σ ρ⋆ =
  subst-comp (abstract2 Ψ As As' p C)

apply⋆ : (Φ : Ctx⋆)(Γ : Ctx Φ)(Ψ Ψ' : Ctx⋆)(Δ  : Ctx Ψ)(Δ' : Ctx Ψ')
  → (Δ' ≤C Δ)
  → (C : Ψ ⊢⋆ *)
  → (σ⋆ : Sub Ψ' Φ)(σ : ITel Δ' Γ σ⋆)
  → Φ ⊢⋆ *
apply⋆ Φ Γ Ψ .Ψ Δ .Δ base C σ⋆ σ = subst σ⋆ C
apply⋆ Φ Γ .(_ ,⋆ _) Ψ' .(_ ,⋆ _) Δ' (skip⋆ p) C σ⋆ σ = apply⋆ Φ Γ _ _ _ Δ' p (Π C) σ⋆ σ 
apply⋆ Φ Γ Ψ Ψ' (_ , A) Δ' (skip p) C σ⋆ σ = apply⋆ Φ Γ _ _ _ _ p (A ⇒ C) σ⋆ σ

data _⊢_ {Φ} (Γ : Ctx Φ) : Φ ⊢⋆ * → Set where

  ` : {A : Φ ⊢⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {K}{B : Φ ,⋆ K ⊢⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {K B}
    → Γ ⊢ Π B
    → (A : Φ ⊢⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{K}
   → (A : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢⋆ K)
   → Γ ⊢ A · ƛ (μ (weaken A) (` Z)) · B
   → Γ ⊢ μ A B

  unwrap : ∀{K}
    → {A : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢⋆ K}
    → Γ ⊢ μ A B
    → Γ ⊢ A · ƛ (μ (weaken A) (` Z)) · B
    
  conv : {A B : Φ ⊢⋆ *}
    → A ≡β B
    → Γ ⊢ A
      -----
    → Γ ⊢ B

  con : ∀{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  builtin : 
      (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : Sub Δ Φ) -- substitutes for new vars introduced by the Sig
    → Tel Γ Δ σ As  -- a telescope of terms M_i typed in subst σ
    -----------------------------
    → Γ ⊢ subst σ C

  pbuiltin :
      (b :  Builtin)
    → let Ψ ,, As ,, C = SIG b in
      ∀ Ψ' → 
      (σ : Sub Ψ' Φ)
    → (As' : List (Ψ' ⊢⋆ *))
    → (p : (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L substEq (λ Φ → List (Φ ⊢⋆ *)) (sym p) As))
    → Tel Γ Ψ' σ As'
    → Γ ⊢ abstract3 Φ Ψ Ψ' As As' p C σ

  ibuiltin : 
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      (σ⋆ : Sub Ψ Φ)
    → (σ : ITel Δ Γ σ⋆)
    → Γ ⊢ subst σ⋆ C

  ipbuiltin : 
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      ∀ Ψ'
    → (Δ' : Ctx Ψ')
    → (p : Δ' ≤C Δ)
      (σ⋆ : Sub Ψ' Φ)
    → (σ : ITel Δ' Γ σ⋆)
    → Γ ⊢ apply⋆ Φ Γ Ψ Ψ' Δ Δ' p C σ⋆ σ

  error : (A : Φ ⊢⋆ *) → Γ ⊢ A


data Tel {Φ} Γ Δ σ where
  []  : Tel Γ Δ σ []
  _∷_ : ∀{A As} → Γ ⊢ subst σ A → Tel Γ Δ σ As →  Tel Γ Δ σ (A ∷ As)


ITel {Φ} Γ Δ σ = {A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ subst σ A

\end{code}

\begin{code}
conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 →  (Γ ∋ A)
 → Γ' ∋ A'
conv∋ refl refl t = t

convTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → Γ ≡ Γ'
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢⋆ J)
  → (As : List (Ψ ⊢⋆ *))
  → Tel Γ Ψ σ As → Tel Γ' Ψ σ As

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

convTel p σ []       []         = []
convTel p σ (A ∷ As) (t ∷ ts) = conv⊢ p refl t ∷ convTel p σ As ts
\end{code}
