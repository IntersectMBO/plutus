\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
open import Data.Sum

open import Type
open import Type.BetaNormal
import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Constant.Type
open import Utils
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  4 _⊢_
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
  ∅    : Ctx ∅
  _,⋆_ : ∀{Φ} → Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_  : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Ctx Φ
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

A variable is indexed by its context and type.
\begin{code}
open import Type.BetaNormal.Equality
data _∋_ : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  Z : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weakenNf A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
open import Data.String

data Tel {Φ} Γ Δ (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J) : List (Δ ⊢Nf⋆ *) → Set

-- this is just a synonym for a substitution
ITel : ∀ {Φ}{Ψ} Γ Δ → SubNf Φ Ψ → Set

ISIG : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢Nf⋆ *
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
ISIG ifThenElse = _ ,, (∅ , con bool ,⋆ * , ne (` Z) , ne (` Z)) ,, ne (` Z)

data _≤C_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → Γ ≤C Γ' → Γ ≤C (Γ' ,⋆ K)
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢Nf⋆ *} → Γ ≤C Γ' → Γ ≤C (Γ' , A)

data _≤C'_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C' Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → (Γ ,⋆ K) ≤C' Γ' → Γ ≤C' Γ'
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ ⊢Nf⋆ *} → (Γ , A) ≤C' Γ' → Γ ≤C' Γ'

postulate ≤C'to≤C : ∀{Φ Φ'}(Γ : Ctx Φ)(Γ' : Ctx Φ') → Γ ≤C Γ' → Γ ≤C' Γ'

abstract2 : ∀ Ψ (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ ⊢Nf⋆ *))(p : As' ≤L As)(C : Ψ ⊢Nf⋆ *) → Ψ ⊢Nf⋆ *
abstract2 Ψ As       .As base     C = C
abstract2 Ψ (A ∷ As) As' (skip p) C = abstract2 Ψ As As' p (A ⇒ C)

abstract1 : ∀ Ψ Ψ' (p : Ψ' ≤C⋆ Ψ)(C : Ψ ⊢Nf⋆ *) → Ψ' ⊢Nf⋆ *
abstract1 Ψ        Ψ  base     C = C
abstract1 (Ψ ,⋆ _) Ψ' (skip p) C = abstract1 Ψ Ψ' p (Π C)

abstractTy : ∀ Ψ Ψ' (p : Ψ' ≤C⋆' Ψ)(C : Ψ ⊢Nf⋆ *) → Ψ' ⊢Nf⋆ *
abstractTy Ψ Ψ  base     C = C
abstractTy Ψ Ψ' (skip p) C = Π (abstractTy Ψ _ p C)

abstractTm : ∀ Ψ (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ ⊢Nf⋆ *))(p : As' ≤L' As)(C : Ψ ⊢Nf⋆ *) → Ψ ⊢Nf⋆ *
abstractTm Ψ As .As base     C = C
abstractTm Ψ As As' (skip {a = A} p) C = A ⇒ abstractTm Ψ As (A ∷ As') p C

abstractArg : ∀ {Φ Ψ Ψ'} → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (Ψ' ≤C⋆' Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L' subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As) → Ψ ⊢Nf⋆ * → (SubNf Ψ' Φ) → Φ ⊢Nf⋆ *
abstractArg As .[] (inj₁ (p ,, refl)) C σ =
  substNf σ (abstractTy _ _ p (abstractTm _ As [] ([]≤L' _) C))
abstractArg As As' (inj₂ (refl ,, q)) C σ =
  substNf σ (abstractTm _ As As' q C) 
{-
abstract3 : ∀ Φ Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As) → Ψ ⊢Nf⋆ * → (SubNf Ψ' Φ) → Φ ⊢Nf⋆ *
abstract3 Φ Ψ Ψ As As' (inj₂ (refl ,, p)) C σ = substNf σ (abstract2 Ψ As As' p C)
abstract3 Φ Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ =
  substNf σ (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C)) 

abstract3' : ∀ Φ Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (Ψ' ≤C⋆' Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As) → Ψ ⊢Nf⋆ * → (SubNf Ψ' Φ) → Φ ⊢Nf⋆ *
abstract3' Φ Ψ Ψ' As As' (inj₁ (p ,, q)) = abstract3 Φ Ψ Ψ' As As' (inj₁ (≤C⋆'to≤C⋆ p ,, q)) 
abstract3' Φ Ψ Ψ' As As' (inj₂ p)        = abstract3 Φ Ψ Ψ' As As' (inj₂ p) 

abstract3-ren : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (p : (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As)) → (C : Ψ ⊢Nf⋆ *) → (σ : SubNf Ψ' Φ) → (ρ⋆ : ⋆.Ren Φ Φ') →
  abstract3 Φ' Ψ Ψ' As As' p
  C (λ x → renNf ρ⋆ (σ x)) 
  ≡
  renNf ρ⋆
  (abstract3 Φ Ψ Ψ' As As' p
   C σ)
abstract3-ren Φ Φ' Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ ρ⋆ =
  renNf-substNf σ ρ⋆ (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C))
abstract3-ren Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, p)) C σ ρ⋆ =
  renNf-substNf σ ρ⋆ (abstract2 Ψ As As' p C)
-}
abstractArg-ren : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (p : (Ψ' ≤C⋆' Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L' subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As)) → (C : Ψ ⊢Nf⋆ *) → (σ : SubNf Ψ' Φ) → (ρ⋆ : ⋆.Ren Φ Φ') →
  abstractArg As As' p
  C (λ x → renNf ρ⋆ (σ x)) 
  ≡
  renNf ρ⋆
  (abstractArg As As' p
   C σ)
abstractArg-ren Φ Φ' Ψ Ψ' As .[] (inj₁ (p ,, refl)) C σ ρ⋆ =
  renNf-substNf σ ρ⋆ (abstractTy Ψ Ψ' p (abstractTm Ψ As [] ([]≤L' As) C))
abstractArg-ren Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, p)) C σ ρ⋆ =
  renNf-substNf σ ρ⋆ (abstractTm Ψ As As' p C)


{-abstract3-subst : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (p : (Ψ' ≤C⋆ Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As)) → (C : Ψ ⊢Nf⋆ *) → (σ : SubNf Ψ' Φ) → (ρ⋆ : SubNf Φ Φ') →
  abstract3 Φ' Ψ Ψ' As As' p
  C (λ x → substNf ρ⋆ (σ x)) 
  ≡
  substNf ρ⋆
  (abstract3 Φ Ψ Ψ' As As' p
   C σ)
abstract3-subst Φ Φ' Ψ Ψ' As As' (inj₁ (p ,, refl)) C σ ρ⋆ =
  substNf-comp σ ρ⋆ (abstract1 Ψ Ψ' p (abstract2 Ψ As [] ([]≤L As) C))
abstract3-subst Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, p)) C σ ρ⋆ =
  substNf-comp σ ρ⋆ (abstract2 Ψ As As' p C)
-}

abstractArg-subst : ∀ Φ Φ' Ψ Ψ' → (As : List (Ψ ⊢Nf⋆ *))(As' : List (Ψ' ⊢Nf⋆ *)) → (p : (Ψ' ≤C⋆' Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L' subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As)) → (C : Ψ ⊢Nf⋆ *) → (σ : SubNf Ψ' Φ) → (ρ⋆ : SubNf Φ Φ') →
  abstractArg As As' p
  C (λ x → substNf ρ⋆ (σ x)) 
  ≡
  substNf ρ⋆
  (abstractArg As As' p
   C σ)
abstractArg-subst Φ Φ' Ψ Ψ' As .[] (inj₁ (p ,, refl)) C σ σ' =
  substNf-comp σ σ' (abstractTy Ψ Ψ' p (abstractTm Ψ As [] ([]≤L' As) C))
abstractArg-subst Φ Φ' Ψ Ψ' As As' (inj₂ (refl ,, q)) C σ σ' =
  substNf-comp σ σ' (abstractTm Ψ As As' q C)

apply⋆ : (Φ : Ctx⋆)(Γ : Ctx Φ)(Ψ Ψ' : Ctx⋆)(Δ  : Ctx Ψ)(Δ' : Ctx Ψ')
  → (Δ' ≤C Δ)
  → (C : Ψ ⊢Nf⋆ *)
  → (σ⋆ : SubNf Ψ' Φ)(σ : ITel Δ' Γ σ⋆)
  → Φ ⊢Nf⋆ *
apply⋆ Φ Γ Ψ .Ψ Δ .Δ base C σ⋆ σ = substNf σ⋆ C
apply⋆ Φ Γ .(_ ,⋆ _) Ψ' .(_ ,⋆ _) Δ' (skip⋆ p) C σ⋆ σ = apply⋆ Φ Γ _ _ _ Δ' p (Π C) σ⋆ σ 
apply⋆ Φ Γ Ψ Ψ' (_ , A) Δ' (skip p) C σ⋆ σ = apply⋆ Φ Γ _ _ _ _ p (A ⇒ C) σ⋆ σ

data _⊢_ {Φ} (Γ : Ctx Φ) : Φ ⊢Nf⋆ * → Set where

  ` : ∀ {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : Φ ⊢Nf⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{K}
   → (A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢Nf⋆ K)
   → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
   → Γ ⊢ μ A B

  unwrap : ∀{K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → Γ ⊢ μ A B
    → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)

  con : ∀{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  builtin :
      (bn : Builtin)
    → let Ψ ,, As ,, C = SIG bn in
      (σ : SubNf Ψ Φ)
    → Tel Γ Ψ σ As
      -------------------------------
    → Γ ⊢ substNf σ C

  pbuiltin :
      (b :  Builtin)
    → let Ψ ,, As ,, C = SIG b in
      ∀ Ψ' → 
      (σ : SubNf Ψ' Φ)
    → (As' : List (Ψ' ⊢Nf⋆ *))
    → (p : (Ψ' ≤C⋆' Ψ × As' ≡ []) ⊎ (Σ (Ψ' ≡ Ψ) λ p →  As' ≤L' subst (λ Φ → List (Φ ⊢Nf⋆ *)) (sym p) As))
    → Tel Γ Ψ' σ As'
    → Γ ⊢ abstractArg As As' p C σ

  ibuiltin : 
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      (σ⋆ : SubNf Ψ Φ)
    → (σ : ITel Δ Γ σ⋆)
    → Γ ⊢ substNf σ⋆ C

  ipbuiltin : 
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      ∀ Ψ'
    → (Δ' : Ctx Ψ')
    → (p : Δ' ≤C Δ)
      (σ⋆ : SubNf Ψ' Φ)
    → (σ : ITel Δ' Γ σ⋆)
    → Γ ⊢ apply⋆ Φ Γ Ψ Ψ' Δ Δ' p C σ⋆ σ

  error : (A : Φ ⊢Nf⋆ *) → Γ ⊢ A

data Tel {Φ} Γ Δ σ where
  []  : Tel Γ Δ σ []
  _∷_ : ∀{A As} → Γ ⊢ substNf σ A → Tel Γ Δ σ As →  Tel Γ Δ σ (A ∷ As)

ITel {Φ} Γ Δ σ = {A : Φ ⊢Nf⋆ *} → Γ ∋ A → Δ ⊢ substNf σ A

\end{code}

Utility functions

\begin{code}
_++T_ : ∀ {Φ Γ Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J}
  → {As : List (Δ ⊢Nf⋆ *)}
  → {As' : List (Δ ⊢Nf⋆ *)}
  → (ts  : Tel Γ Δ σ As)
  → (ts' : Tel Γ Δ σ As')
  → Tel Γ Δ σ (As Data.List.++ As')
[]       ++T ts' = ts'
(t ∷ ts) ++T ts' = t ∷ (ts ++T ts')


_:<T_ : ∀ {Φ Γ Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J}
  → {As : List (Δ ⊢Nf⋆ *)}
  → {A  : Δ ⊢Nf⋆ *}
  → (ts : Tel Γ Δ σ As)
  → (t : Γ ⊢ substNf σ A)
  → Tel Γ Δ σ (As :<L A)
[]        :<T t = t ∷ []
(t' ∷ ts) :<T t = t' ∷ (ts :<T t)

open import Type.BetaNormal.Equality

conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ∋ A
 → Γ' ∋ A'
conv∋ refl refl x = x

open import Type.BetaNBE.Completeness
open import Type.Equality
open import Type.BetaNBE.RenamingSubstitution

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

convTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → Γ ≡ Γ'
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (As : List (Ψ ⊢Nf⋆ *))
  → Tel Γ Ψ σ As → Tel Γ' Ψ σ As
convTel p σ []       []       = []
convTel p σ (A ∷ As) (t ∷ ts) = conv⊢ p refl t ∷ convTel p σ As ts
\end{code}
