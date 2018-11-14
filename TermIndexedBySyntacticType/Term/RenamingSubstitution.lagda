\begin{code}
module TermIndexedBySyntacticType.Term.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Type
import Type.RenamingSubstitution as ⋆
open import Type.Equality
open import Builtin.Signature
open import Builtin.Constant.Term
open import TermIndexedBySyntacticType.Term
\end{code}


## Renaming

\begin{code}
ext : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ ⋆.rename ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K } {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
     → Γ , B ∋ A
       -------------------------------
     → Δ , ⋆.rename ρ⋆ B ∋ ⋆.rename ρ⋆ A)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
ext⋆ : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ ⋆.rename ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ∋ ⋆.rename (⋆.ext ρ⋆) A )
ext⋆ {Γ}{Δ} ρ⋆ ρ {J}{K}{A} (T x) =
  substEq (λ A → Δ ,⋆ K ∋ A)
          (trans (sym (⋆.rename-comp _)) (⋆.rename-comp _))
          (T (ρ x))
\end{code}

\begin{code}
renameTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.rename ρ⋆ A ))
renameTermCon ρ⋆ (integer s i p)    = integer s i p
renameTermCon ρ⋆ (bytestring s b p) = bytestring s b p
renameTermCon ρ⋆ (size s)           = size s
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.List

rename : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {J} → ∥ Γ ∥ ∋⋆ J → ∥ Δ ∥ ∋⋆ J)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ ⋆.rename ρ⋆ A)
    ------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Δ ⊢ ⋆.rename ρ⋆ A )
rename ρ⋆ ρ (` x)    = ` (ρ x)
rename ρ⋆ ρ (ƛ N)    = ƛ (rename ρ⋆ (ext ρ⋆ ρ) N)
rename ρ⋆ ρ (L · M)  = rename ρ⋆ ρ L · rename ρ⋆ ρ M 
rename ρ⋆ ρ (Λ N)    = Λ (rename (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N )
rename {Γ}{Δ} ρ⋆ ρ (_·⋆_ {B = B} t A) =
  substEq (λ A → Δ ⊢ A)
          ( trans (sym (⋆.subst-rename B))
                 (trans (⋆.subst-cong (⋆.rename-subst-cons ρ⋆ A) B)
                        (⋆.rename-subst B) ) )
          (rename ρ⋆ ρ t ·⋆ ⋆.rename ρ⋆ A)
rename ρ⋆ ρ (wrap1 pat arg t) = wrap1 _ _ (rename ρ⋆ ρ t)
rename ρ⋆ ρ (unwrap1 t)       = unwrap1 (rename ρ⋆ ρ t)
rename ρ⋆ ρ (conv p t) = conv (rename≡β ρ⋆ p) (rename ρ⋆ ρ t)
rename ρ⋆ ρ (con cn)   = con (renameTermCon ρ⋆ cn)
rename {Γ}{Δ} ρ⋆ ρ (builtin bn σ X σ') = substEq
  (Δ ⊢_)
  (⋆.rename-subst (⋆.subst σ (proj₂ (proj₂ (SIG bn ∅)))))
  (builtin bn σ X (⋆.rename ρ⋆ ∘ σ'))
rename ρ⋆ ρ (error A) = error (⋆.rename ρ⋆ A)
\end{code}

\begin{code}
weaken : ∀ {Φ J}{A : ∥ Φ ∥ ⊢⋆ J}{K}{B : ∥ Φ ∥ ⊢⋆ K}
  → Φ ⊢ A
    -------------
  → Φ , B ⊢ A
weaken {Φ}{J}{A}{K}{B} x =
  substEq (λ x → Φ , B ⊢ x)
          (⋆.rename-id A)
          (rename id
                  (λ x → substEq (λ A → Φ , B ∋ A) (sym (⋆.rename-id _)) (S x))
                  x)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ J}{A : ∥ Φ ∥ ⊢⋆ J}{K}
  → Φ ⊢ A
    ------------------
  → Φ ,⋆ K ⊢ ⋆.weaken A
weaken⋆ x = rename _∋⋆_.S _∋_.T x
\end{code}

## Substitution
\begin{code}
exts : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
     → Γ , B ∋ A
     -------------------------------
     → Δ , ⋆.subst σ⋆ B ⊢ ⋆.subst σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ ⋆.subst (⋆.exts σ⋆) A )
exts⋆ {Γ}{Δ} σ⋆ σ {J}{K}(T {A = A} x) =
  substEq (λ x → Δ ,⋆ K ⊢ x)
          (trans (sym (⋆.rename-subst A))
                 (⋆.subst-rename A))
          (weaken⋆ (σ x))

\end{code}

\begin{code}
substTermCon : ∀ {Φ Ψ}
  → (σ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    ------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.subst σ⋆ A ))
substTermCon σ⋆ (integer s i p)    = integer s i p
substTermCon σ⋆ (bytestring s b p) = bytestring s b p
substTermCon σ⋆ (size s)           = size s
\end{code}


\begin{code}
subst : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Δ ⊢ ⋆.subst σ⋆ A)
subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ N)                     = ƛ (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst σ⋆ σ (Λ N)                     = Λ (subst (⋆.exts σ⋆) (exts⋆ σ⋆ σ) N)
subst {Γ}{Δ} σ⋆ σ (_·⋆_ {B = B} L M) =
  substEq (λ A → Δ ⊢ A)
          (trans (sym (⋆.subst-comp B))
                 (trans (⋆.subst-cong (⋆.subst-subst-cons σ⋆ M)
                                    B)
                        (⋆.subst-comp B)))
          (subst σ⋆ σ L ·⋆ ⋆.subst σ⋆ M)
subst σ⋆ σ (wrap1 pat arg t) = wrap1 _ _ (subst σ⋆ σ t)
subst σ⋆ σ (unwrap1 t)       = unwrap1 (subst σ⋆ σ t)
subst σ⋆ σ (conv p t) = conv (subst≡β σ⋆ p) (subst σ⋆ σ t)
subst σ⋆ σ (con cn) = con (substTermCon σ⋆ cn)
subst {Γ}{Δ} σ⋆ σ (builtin bn σ' tel σ'') = substEq
  (Δ ⊢_)
  (⋆.subst-comp (⋆.subst σ' (proj₂ (proj₂ (SIG bn ∅)))))
  (builtin bn σ' tel (⋆.subst σ⋆ ∘ σ''))
subst σ⋆ σ (error A) = error (⋆.subst σ⋆ A)
\end{code}

\begin{code}

substcons : ∀{Γ Δ} →
  (σ⋆ : ∀{K} → ∥ Γ ∥  ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J}{A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
  → ∀{J}{A : ∥ Γ ∥ ⊢⋆ J}
  → (t : Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------
  → (∀ {J} {B : ∥ Γ ∥ ⊢⋆ J} → Γ , A ∋ B → Δ ⊢ ⋆.subst σ⋆ B)
substcons σ⋆ σ t Z     = t
substcons σ⋆ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀ {J Γ} {A B : ∥ Γ ∥ ⊢⋆ J}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_]  {J} {Γ}{A}{B} t s =
  substEq (λ A → Γ ⊢ A)
          (⋆.subst-id A)
          (subst `
                 (substcons `
                            (λ x → substEq (λ A → Γ ⊢ A)
                                           (sym (⋆.subst-id _))
                                           (` x))
                            (substEq (λ A → Γ ⊢ A) (sym (⋆.subst-id B)) s))
                 t) 
\end{code}

\begin{code}
_[_]⋆ : ∀ {J Γ K} {B : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
        → Γ ,⋆ K ⊢ B
        → (A : ∥ Γ ∥ ⊢⋆ K)
          ---------
        → Γ ⊢ B ⋆.[ A ]
_[_]⋆ {J}{Γ}{K}{B} t A =
  subst (⋆.subst-cons ` A)
        (λ{(T {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (sym (⋆.subst-id A'))
                                     (⋆.subst-rename A'))
                                     (` x)})
          t
\end{code}
