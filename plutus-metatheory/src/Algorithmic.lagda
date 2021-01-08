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

data _≤C_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → Γ ≤C Γ' → Γ ≤C (Γ' ,⋆ K)
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ' ⊢Nf⋆ *} → Γ ≤C Γ' → Γ ≤C (Γ' , A)

∅≤C : ∀ {Φ} → (Γ : Ctx Φ) → ∅ ≤C Γ
∅≤C ∅       = base
∅≤C (Γ ,⋆ K) = skip⋆ (∅≤C Γ)
∅≤C (Γ , A) = skip (∅≤C Γ)

data _≤C'_ {Φ}(Γ : Ctx Φ) : ∀{Φ'} → Ctx Φ' → Set where
 base : Γ ≤C' Γ
 skip⋆ : ∀{Φ'}{Γ' : Ctx Φ'}{K} → (Γ ,⋆ K) ≤C' Γ' → Γ ≤C' Γ'
 skip : ∀{Φ'}{Γ' : Ctx Φ'}{A : Φ ⊢Nf⋆ *} → (Γ , A) ≤C' Γ' → Γ ≤C' Γ'

skip⋆' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{K} → Γ ≤C' Γ' → Γ ≤C' (Γ' ,⋆ K)
skip⋆' base = skip⋆ base
skip⋆' (skip⋆ p) = skip⋆ (skip⋆' p)
skip⋆' (skip p) = skip (skip⋆' p)

skip' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'}{A} → Γ ≤C' Γ' → Γ ≤C' (Γ' , A)
skip' base = skip base
skip' (skip⋆ p) = skip⋆ (skip' p)
skip' (skip p) = skip (skip' p)

≤Cto≤C' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'} → Γ ≤C Γ' → Γ ≤C' Γ'
≤Cto≤C' base      = base
≤Cto≤C' (skip⋆ p) = skip⋆' (≤Cto≤C' p)
≤Cto≤C' (skip p)  = skip' (≤Cto≤C' p)

∅≤C' : ∀ {Φ} → (Γ : Ctx Φ) → ∅ ≤C' Γ
∅≤C' Γ = ≤Cto≤C' (∅≤C Γ)

ISIG : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢Nf⋆ *
ISIG ifThenElse = ∅ ,⋆ * ,, ∅ ,⋆ * , con bool , ne (` Z) , ne (` Z) ,, ne (` Z)
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

isig2type : (Φ : Ctx⋆) → Ctx Φ → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
isig2type .∅ ∅ C = C
isig2type (Φ ,⋆ J) (Γ ,⋆ J) C = isig2type Φ Γ (Π C)
isig2type Φ        (Γ ,  A) C = isig2type Φ Γ (A ⇒ C)

itype : ∀{Φ} → Builtin → Φ ⊢Nf⋆ *
itype b = let Φ ,, Γ ,, C = ISIG b in subNf (λ()) (isig2type Φ Γ C) 

postulate itype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → itype b ≡ renNf ρ (itype b)
postulate itype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → itype b ≡ subNf ρ (itype b)

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

  ibuiltin : (b :  Builtin) → Γ ⊢ itype b

  error : (A : Φ ⊢Nf⋆ *) → Γ ⊢ A

\end{code}

Utility functions

\begin{code}
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

<C'2type : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'} → Γ ≤C' Γ' → Φ' ⊢Nf⋆ * → Φ ⊢Nf⋆ *
<C'2type base      C = C
<C'2type (skip⋆ p) C = Π (<C'2type p C)
<C'2type (skip {A = A} p)  C = A ⇒ <C'2type p C

Ctx2type : ∀{Φ}(Γ : Ctx Φ) → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
Ctx2type ∅        C = C
Ctx2type (Γ ,⋆ J) C = Ctx2type Γ (Π C)
Ctx2type (Γ , x)  C = Ctx2type Γ (x ⇒ C)

Πlem : ∀{K K'}{Φ Φ'}{Δ : Ctx Φ'}{Γ : Ctx Φ}(p : ((Δ ,⋆ K) ,⋆ K') ≤C' Γ)
  (A : ∅ ⊢Nf⋆ K)(C : Φ ⊢Nf⋆ *)(σ : SubNf Φ' ∅)
  → (Π
       (eval
        (⋆.sub (⋆.exts (⋆.exts (λ x → embNf (σ x))))
         (embNf (<C'2type p C)))
        (exte (exte (idEnv ∅))))
       [ A ]Nf)
      ≡ subNf (subNf-cons σ A) (Π (<C'2type p C))
Πlem p A C σ = sym (subNf-cons-[]Nf (Π (<C'2type p C)))

⇒lem : ∀{K}{A : ∅ ⊢Nf⋆ K}{Φ Φ'}{Δ : Ctx Φ'}{Γ : Ctx Φ}{B : Φ' ,⋆ K ⊢Nf⋆ *}
       (p : ((Δ ,⋆ K) , B) ≤C' Γ)(σ : SubNf Φ' ∅)(C : Φ ⊢Nf⋆ *)
  → ((eval (⋆.sub (⋆.exts (λ x → embNf (σ x))) (embNf B))
        (exte (idEnv ∅))
        ⇒
        eval (⋆.sub (⋆.exts (λ x → embNf (σ x))) (embNf (<C'2type p C)))
        (exte (idEnv ∅)))
       [ A ]Nf)
      ≡ subNf (subNf-cons σ A) (B ⇒ <C'2type p C)
⇒lem {B = B} p σ C = sym (subNf-cons-[]Nf (B ⇒ <C'2type p C)) 
\end{code}
