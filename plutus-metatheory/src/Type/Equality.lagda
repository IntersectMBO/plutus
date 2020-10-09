\begin{code}
module Type.Equality where
\end{code}

## Fixity

\begin{code}
infix  1 _≡β_
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
\end{code}

## Beta equality relation for types

This serves as a declaritive specification of the semantics of types.

We need to give constructors for reflexivity, symmetry and
transitivity as the presence of the beta-rule prevents these
properties from being derivable. We have congruence rules for all
constructors of type (except variables as this is subsumed by
reflexivity). Finally, we have one computation rule: the beta-rule for
application.

\begin{code}
data _≡β_ {Φ} : ∀{J} → Φ ⊢⋆ J → Φ ⊢⋆ J → Set where

  -- structural rules

  refl≡β  : ∀{J}
    → (A : Φ ⊢⋆ J)
      ------------
    → A ≡β A
    
  sym≡β   : ∀{J}{A B : Φ ⊢⋆ J}
    → A ≡β B
      ------
    → B ≡β A
  trans≡β : ∀{J}{A B C : Φ ⊢⋆ J}
    → A ≡β B
    → B ≡β C
      ------
    → A ≡β C

  -- congruence rules

  -- (no variable rule is needed)
 
  ⇒≡β : {A A' B B' : Φ ⊢⋆ *}
    → A ≡β A'
    → B ≡β B'
      ---------------------
    → (A ⇒ B) ≡β (A' ⇒ B')
    
  Π≡β : ∀{J}{B B' : Φ ,⋆ J ⊢⋆ *}
    → B ≡β B'
      -------
    → Π B ≡β Π B'
    
  ƛ≡β : ∀{K J}{B B' : Φ ,⋆ J ⊢⋆ K}
    → B ≡β B'
      ---------------
    → ƛ B ≡β ƛ B'
    
  ·≡β : ∀{K J}{A A' : Φ ⊢⋆ K ⇒ J}{B B' : Φ ⊢⋆ K}
    → A ≡β A'
    → B ≡β B'
      --------------------
    → A · B ≡β A' · B'
    
  μ≡β : ∀{K}{A A'}{B B' : Φ ⊢⋆ K}
    → A ≡β A'
    → B ≡β B'
      ----------------
    → μ A B ≡β μ A' B'
    
  -- computation rule

  β≡β : ∀{K J}
    → (B : Φ ,⋆ J ⊢⋆ K)
    → (A : Φ ⊢⋆ J)
      ------------------------
    → ƛ B · A ≡β B [ A ]
    
\end{code}

Let `p` and `q` range over proofs of type equality.

\begin{code}
≡2β : ∀{Φ K}{A A' : Φ ⊢⋆ K} → A ≡ A' → A ≡β A'
≡2β refl = refl≡β _
\end{code}

## Renaming for proofs of type equality

\begin{code}
ren≡β : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A ≡β B
    ----------------------------
  → ren ρ A ≡β ren ρ B
ren≡β ρ (refl≡β A)    = refl≡β (ren ρ A)
ren≡β ρ (sym≡β p)     = sym≡β (ren≡β ρ p)
ren≡β ρ (trans≡β p q) = trans≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (⇒≡β p q)     = ⇒≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (Π≡β p)       = Π≡β (ren≡β (ext ρ) p)
ren≡β ρ (ƛ≡β p)       = ƛ≡β (ren≡β (ext ρ) p)
ren≡β ρ (·≡β p q)     = ·≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (μ≡β p q)     = μ≡β (ren≡β ρ p) (ren≡β ρ q)
ren≡β ρ (β≡β B A)     = trans≡β
  (β≡β _ _)
  (≡2β (trans (sym (subst-ren B))
              (trans (subst-cong (ren-subst-cons ρ A) B)
                     (ren-subst B))))
\end{code}

## Substitution for proofs of type equality

\begin{code}
subst≡β : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
 → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → A ≡β B
    ----------------------------
  → subst σ A ≡β subst σ B
subst≡β σ (refl≡β A)    = refl≡β (subst σ A)
subst≡β σ (sym≡β p)     = sym≡β (subst≡β σ p)
subst≡β σ (trans≡β p q) = trans≡β (subst≡β σ p) (subst≡β σ q) 
subst≡β σ (⇒≡β p q)     = ⇒≡β (subst≡β σ p) (subst≡β σ q)
subst≡β σ (Π≡β p)       = Π≡β (subst≡β (exts σ) p)
subst≡β σ (ƛ≡β p)       = ƛ≡β (subst≡β (exts σ) p)
subst≡β σ (·≡β p q)     = ·≡β (subst≡β σ p) (subst≡β σ q)
subst≡β σ (μ≡β p q)     = μ≡β (subst≡β σ p) (subst≡β σ q)
subst≡β σ (β≡β B A)     = trans≡β
  (β≡β _ _)
  (≡2β (trans (trans (sym (subst-comp B))
                     (subst-cong (subst-subst-cons σ A) B))
              (subst-comp B)))
\end{code}

