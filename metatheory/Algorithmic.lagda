\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)

open import Type
open import Type.BetaNormal

open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf 
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
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

  Z : ∀ {Φ Γ} {A B : Φ ⊢Nf⋆ *}
    → A ≡Nf B
      ----------
    → Γ , A ∋ B

  S : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ *}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ∋ A
    → weakenNf A ≡Nf B
      -------------------
    → Γ ,⋆ K ∋ B
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
open import Data.String

Tel : ∀ {Φ} Γ Δ → (∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J) → List (Δ ⊢Nf⋆ *) → Set

data _⊢_ : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  ` : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → String
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Φ Γ K}
    → (x : String)
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π x B

  ·⋆ : ∀ {Φ Γ K x}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → {C : Φ ⊢Nf⋆ *}
    → Γ ⊢ Π x B
    → (A : Φ ⊢Nf⋆ K)
    → (B [ A ]) ≡Nf C
      ---------------
    → Γ ⊢ C

  wrap1 : ∀{Φ Γ K}
   → (pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : Φ ⊢Nf⋆ K)
   → (term : Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg))
   → Γ ⊢ ne (μ1 · pat · arg)

  unwrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → (term : Γ ⊢ ne (μ1 · pat · arg))
    → {B : Φ ⊢Nf⋆ *}
    → nf (embNf pat · (μ1 · embNf pat) · embNf arg) ≡Nf B
    → Γ ⊢ B 

  con : ∀{Φ}{Γ : Ctx Φ}{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  builtin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
    → Tel Γ Δ σ As
    → {B : Φ ⊢Nf⋆ *}
    → substNf σ C ≡Nf B
      -------------------------------
    → Γ ⊢ B

  error : ∀{Φ Γ} → (A : Φ ⊢Nf⋆ *) → Γ ⊢ A

Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ substNf σ A × Tel Γ Δ σ As

\end{code}

# Term Abbreviations
\begin{code}
--void : ∀{Γ} → Γ ⊢ unitNf
--void = Λ (ƛ (` Z))

true : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ booleanNf
true = Λ "α" (ƛ "t" (ƛ "f" (` (S (Z reflNf)))))

false : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ booleanNf
false = Λ "α" (ƛ "t" (ƛ "f" (` (Z reflNf))))
\end{code}

Utility functions

\begin{code}
open import Type.BetaNormal.Equality


data _≡Ctx_ : ∀{Φ} → Ctx Φ → Ctx Φ → Set where
  ∅ : ∅ ≡Ctx ∅
  _,⋆_ : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → ∀ K → (Γ ,⋆ K) ≡Ctx (Γ' ,⋆ K)
  _,_  : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → {A A' : Φ ⊢Nf⋆ *} → A ≡Nf A'
    → (Γ , A) ≡Ctx (Γ' , A')

reflCtx : ∀{Φ}{Γ : Ctx Φ} → Γ ≡Ctx Γ
reflCtx {Γ = ∅} = ∅
reflCtx {Γ = Γ ,⋆ J} = reflCtx ,⋆ J
reflCtx {Γ = Γ , A} = reflCtx , reflNf

conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡Ctx Γ'
 → A ≡Nf A'
 →  (Γ ∋ A)
 → Γ' ∋ A'
conv∋ (p , q) r (Z s) = Z (transNf (symNf q) (transNf s r))
conv∋ (p , q) r (S α) = S (conv∋ p r α)
conv∋ (p  ,⋆ K) q (T α r) = T (conv∋ p reflNf α) (transNf r q)

open import Type.BetaNBE.Completeness
open import Type.Equality
open import Type.BetaNBE.RenamingSubstitution

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡Ctx Γ'
 → A ≡Nf A'
 → Γ ⊢ A
 → Γ' ⊢ A'

convTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → Γ ≡Ctx Γ'
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (As : List (Ψ ⊢Nf⋆ *))
  → Tel Γ Ψ σ As → Tel Γ' Ψ σ As
convTel p σ []       tt        = tt
convTel p σ (A ∷ As) (t ,, ts) = conv⊢ p reflNf t ,, convTel p σ As ts

conv⊢ p q          (` x)             = ` (conv∋ p q x)
conv⊢ p (⇒≡Nf q r) (ƛ x t)           = ƛ x (conv⊢ (p , q) r t)
conv⊢ p q          (t · u)           =
  conv⊢ p (⇒≡Nf reflNf q) t · conv⊢ p reflNf u
conv⊢ p (Π≡Nf q)   (Λ x t)           = Λ _ (conv⊢ (p ,⋆ _) q t)
conv⊢ p q          (·⋆ t A r)        = ·⋆ (conv⊢ p reflNf t) A (transNf r q) 
conv⊢ p (ne≡Nf (·≡Ne {B' = arg'} (·≡Ne {B' = pat'} μ≡Ne q) r)) (wrap1 pat arg t)
  =
  wrap1
    _
    _
    (conv⊢ p (completeness
        {s = embNf pat · (μ1 · embNf pat) · embNf arg}
        {t = embNf pat'  · (μ1 · embNf pat') · embNf arg'}
        (α2β (·≡α (·≡α (embNf-cong q) (·≡α μ≡α (embNf-cong q)))
                  (embNf-cong r)))) t)
conv⊢ p q          (unwrap1 t r)       =
  unwrap1 (conv⊢ p reflNf t) (transNf r q)
conv⊢ p con≡Nf     (con c)             = con c
conv⊢ p q          (builtin bn σ ts r) =
  builtin bn σ (convTel p σ _ ts) (transNf r q)
conv⊢ p q          (error A)           = error _
\end{code}
