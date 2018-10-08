\begin{code}
module Type.Equality where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Type
open import Type.RenamingSubstitution
\end{code}
## Beta equality relation for types

\begin{code}
data _≡β_ {Γ} : ∀{J} → Γ ⊢⋆ J → Γ ⊢⋆ J → Set where
  refl≡β  : ∀{J}(A : Γ ⊢⋆ J) → A ≡β A
  sym≡β   : ∀{J}{A B : Γ ⊢⋆ J} → A ≡β B → B ≡β A
  trans≡β : ∀{J}{A B C : Γ ⊢⋆ J} → A ≡β B → B ≡β C → A ≡β C

  `≡β : ∀{J}{x : Γ ∋⋆ J} → (` x) ≡β (` x)
  ⇒≡β : {A A' B B' : Γ ⊢⋆ *} → A ≡β A' → B ≡β B' → (A ⇒ B) ≡β (A' ⇒ B')
  Π≡β : ∀{J}{B B' : Γ ,⋆ J ⊢⋆ *} → B ≡β B' → (Π B) ≡β (Π B')
  ƛ≡β : ∀{K J}{B B' : Γ ,⋆ J ⊢⋆ K} → B ≡β B' → (ƛ B) ≡β (ƛ B')
  ·≡β : ∀{K J}{A A' : Γ ⊢⋆ K ⇒ J}{B B' : Γ ⊢⋆ K}
    → A ≡β A'
    → B ≡β B'
    → (A · B) ≡β (A' · B')
  μ≡β : ∀{K}{B B' : Γ ,⋆ K ⊢⋆ K} → B ≡β B' → (μ B) ≡β (μ B')

  β≡β : ∀{K J}{B : Γ ,⋆ J ⊢⋆ K}{A : Γ ⊢⋆ J} → ((ƛ B) · A) ≡β (B [ A ])
\end{code}

## Renaming for proofs of type equality

\begin{code}
rename≡β : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A ≡β B
    ----------------------------
  → rename ρ A ≡β rename ρ B
rename≡β ρ (refl≡β A)    = refl≡β (rename ρ A)
rename≡β ρ (sym≡β p)     = sym≡β (rename≡β ρ p)
rename≡β ρ (trans≡β p q) = trans≡β (rename≡β ρ p) (rename≡β ρ q)
rename≡β ρ `≡β           = refl≡β _
rename≡β ρ (⇒≡β p q)     = ⇒≡β (rename≡β ρ p) (rename≡β ρ q)
rename≡β ρ (Π≡β p)       = Π≡β (rename≡β (ext ρ) p)
rename≡β ρ (ƛ≡β p)       = ƛ≡β (rename≡β (ext ρ) p)
rename≡β ρ (·≡β p q)     = ·≡β (rename≡β ρ p) (rename≡β ρ q)
rename≡β ρ (μ≡β p)       = μ≡β (rename≡β (ext ρ) p)
rename≡β ρ (β≡β {B = B}{A = A}) =
  substEq (λ X → rename ρ ((ƛ B) · A) ≡β X)
          (trans (sym (subst-rename (ext ρ) (subst-cons ` (rename ρ A)) B))
                 (trans (subst-cong _ _ (rename-subst-cons ρ A) B)
                        (rename-subst (subst-cons ` A) ρ B)))
         β≡β
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
subst≡β σ `≡β           = refl≡β _
subst≡β σ (⇒≡β p q)     = ⇒≡β (subst≡β σ p) (subst≡β σ q)
subst≡β σ (Π≡β p)       = Π≡β (subst≡β (exts σ) p)
subst≡β σ (ƛ≡β p)       = ƛ≡β (subst≡β (exts σ) p)
subst≡β σ (·≡β p q)     = ·≡β (subst≡β σ p) (subst≡β σ q)
subst≡β σ (μ≡β p)       = μ≡β (subst≡β (exts σ) p)
subst≡β σ (β≡β {B = B}{A = A}) =
  substEq (λ X → subst σ ((ƛ B) · A) ≡β X)
          (trans (trans (sym (subst-comp (exts σ)
                                         (subst-cons ` (subst σ A))
                                         B))
                        (subst-cong _
                                    _
                                    (subst-subst-cons σ A) B))
          (subst-comp (subst-cons ` A) σ B))
          β≡β
\end{code}
