
\begin{code}
module Declarative where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality
open import Builtin
open import Utils

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
open import Data.Sum
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

data _≤C_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → Γ ≤C Γ' → Γ ≤C (Γ' ,⋆ K)
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢⋆ *} → Γ ≤C Γ' → Γ ≤C (Γ' , A)

ISIG : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢⋆ *
ISIG ifThenElse = ∅ ,⋆ * ,, ∅ ,⋆ * , con bool , ` Z , ` Z ,, ` Z
ISIG addInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG subtractInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG multiplyInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG divideInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG quotientInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG remainderInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG modInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG lessThanInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG lessThanEqualsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG greaterThanInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG greaterThanEqualsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG equalsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG concatenate = ∅ ,, ∅ , con bytestring , con bytestring ,, con bytestring
ISIG takeByteString = ∅ ,, ∅ , con integer , con bytestring ,, con bytestring
ISIG dropByteString = ∅ ,, ∅ , con integer , con bytestring ,, con bytestring
ISIG sha2-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
ISIG sha3-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
ISIG verifySignature = ∅ ,, ∅ , con bytestring , con bytestring , con bytestring ,, con bool
ISIG equalsByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool 
ISIG charToString = ∅ ,, ∅ , con char ,, con string
ISIG append = ∅ ,, ∅ , con string , con string ,, con string
ISIG trace = ∅ ,, ∅ , con string ,, con unit

isig2type : (Φ : Ctx⋆) → Ctx Φ → Φ ⊢⋆ * → ∅ ⊢⋆ *
isig2type .∅ ∅ C = C
isig2type (Φ ,⋆ J) (Γ ,⋆ J) C = isig2type Φ Γ (Π C)
isig2type Φ        (Γ ,  A) C = isig2type Φ Γ (A ⇒ C)

itype : ∀{Φ} → Builtin → Φ ⊢⋆ *
itype b = let Φ ,, Γ ,, C = ISIG b in subst (λ()) (isig2type Φ Γ C) 

postulate itype-ren : ∀{Φ Ψ} b (ρ : Ren Φ Ψ) → itype b ≡ ren ρ (itype b)
postulate itype-subst : ∀{Φ Ψ} b (ρ : Sub Φ Ψ) → itype b ≡ subst ρ (itype b)

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

  ibuiltin : (b :  Builtin) → Γ ⊢ itype b

  error : (A : Φ ⊢⋆ *) → Γ ⊢ A


data Tel {Φ} Γ Δ σ where
  []  : Tel Γ Δ σ []
  _∷_ : ∀{A As} → Γ ⊢ subst σ A → Tel Γ Δ σ As →  Tel Γ Δ σ (A ∷ As)
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
