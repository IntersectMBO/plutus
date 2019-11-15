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
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con boolean
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
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
  Z : ∀ {Φ Γ}{A B : Φ ⊢⋆ *}
    → A ≡α B
      ----------
    → Γ , A ∋ B

  S : ∀ {Φ Γ} {A B : Φ ⊢⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K} {A : Φ ⊢⋆ *}{B : Φ ,⋆ K ⊢⋆ *}
    → Γ ∋ A
    → weaken A ≡α B
      -------------------
    → Γ ,⋆ K ∋ B
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.

\begin{code}
Tel : ∀ {Γ⋆} Γ Δ → Sub Δ Γ⋆ → List (Δ ⊢⋆ *) → Set

data _⊢_ {Φ} (Γ : Ctx Φ) : Φ ⊢⋆ * → Set where

  ` : {A : Φ ⊢⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {A B}
    → String
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {K}{B : Φ ,⋆ K ⊢⋆ *}
    → (x : String)
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π x B

  ·⋆ : ∀ {K B x}
    → Γ ⊢ Π x B
    → {C : Φ ⊢⋆ *}
    → (A : Φ ⊢⋆ K)
    → (B [ A ]) ≡α C
      ---------------
    → Γ ⊢ C

  wrap1 : ∀{K}
   → (pat : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : Φ ⊢⋆ K)
   → (term : Γ ⊢ pat · (μ1 · pat) · arg)
   → Γ ⊢ μ1 · pat · arg

  unwrap1 : ∀{K}
    → {pat pat' : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢⋆ K}
    → (term : Γ ⊢ μ1 · pat · arg)
    → pat ≡α pat'
    → Γ ⊢ pat · (μ1 · pat') · arg
    
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
    → Tel Γ Δ σ As     -- a telescope of terms M_i typed in subst σ
    → {B : Φ ⊢⋆ *}
    → subst σ C ≡α B
    -----------------------------
    → Γ ⊢ B

  error : (A : Φ ⊢⋆ *) → Γ ⊢ A

Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ subst σ A × Tel Γ Δ σ As
\end{code}

Smart constructors

\begin{code}
Z' : ∀ {Φ Γ}{A : Φ ⊢⋆ *} → Γ , A ∋ A
Z' = Z reflα

_·⋆'_ : ∀ {Φ Γ K B x}
    → Γ ⊢ Π x B
    → (A : Φ ⊢⋆ K)
      ---------------
    → Γ ⊢ B [ A ]
_·⋆'_ t A = ·⋆ t A reflα

T' : ∀ {Φ Γ K} {A : Φ ⊢⋆ *}
  → Γ ∋ A
    -------------------
  → Γ ,⋆ K ∋ weaken A
T' x = T x reflα 
\end{code}

\begin{code}
data _≡Ctx_ : ∀{Φ} → Ctx Φ → Ctx Φ → Set where
  ∅ : ∅ ≡Ctx ∅
  _,⋆_ : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → ∀ K → (Γ ,⋆ K) ≡Ctx (Γ' ,⋆ K)
  _,_  : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → {A A' : Φ ⊢⋆ *} → A ≡α A'
    → (Γ , A) ≡Ctx (Γ' , A')

reflCtx : ∀{Φ}{Γ : Ctx Φ} → Γ ≡Ctx Γ
reflCtx {Γ = ∅} = ∅
reflCtx {Γ = Γ ,⋆ J} = reflCtx ,⋆ J
reflCtx {Γ = Γ , A} = reflCtx , reflα
\end{code}

\begin{code}
conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢⋆ *}
 → Γ ≡Ctx Γ'
 → A ≡α A'
 →  (Γ ∋ A)
 → Γ' ∋ A'
conv∋ (p , p') q (Z r) = Z (transα (symα p') (transα r q))
conv∋ (p , p') q (S x) = S (conv∋ p q x)
conv∋ (p ,⋆ K) q (T x r) = T (conv∋ p reflα x) (transα r q)

convTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → Γ ≡Ctx Γ'
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢⋆ J)
  → (As : List (Ψ ⊢⋆ *))
  → Tel Γ Ψ σ As → Tel Γ' Ψ σ As

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢⋆ *}
 → Γ ≡Ctx Γ'
 → A ≡α A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ p q (` x)             = ` (conv∋ p q x)
conv⊢ p (⇒≡α q q') (ƛ x t)  = ƛ x (conv⊢ (p , q) q' t)
conv⊢ p q (t · u)           = conv⊢ p (⇒≡α reflα q) t · conv⊢ p reflα u
conv⊢ p (Π≡α q) (Λ x t)     = Λ _ (conv⊢ (p ,⋆ _) q t) 
conv⊢ p q (·⋆ t A r)        = ·⋆ (conv⊢ p reflα t) A (transα r q)
conv⊢ p (·≡α (·≡α μ≡α q) q') (wrap1 pat arg t) =
  wrap1 _ _ (conv⊢ p (·≡α (·≡α q (·≡α μ≡α q)) q') t)
conv⊢ p (·≡α (·≡α q (·≡α μ≡α q')) q'') (unwrap1 t r) =
  unwrap1 (conv⊢ p (·≡α (·≡α μ≡α q) q'') t) (transα (symα q) (transα r q'))
conv⊢ p q (conv r t)        = conv (trans≡β r (α2β q)) (conv⊢ p reflα t)
conv⊢ p con≡α (con c)       = con c
conv⊢ p q (builtin bn σ ts r) = builtin bn σ (convTel p σ _ ts) (transα r q)
conv⊢ p q (error A)         = error _

convTel p σ []       _         = tt
convTel p σ (A ∷ As) (t ,, ts) = conv⊢ p reflα t ,, convTel p σ As ts
\end{code}
