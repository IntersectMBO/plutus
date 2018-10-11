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
          (trans (sym (⋆.rename-comp ρ⋆ S _)) (⋆.rename-comp S (⋆.ext ρ⋆) _))
          (T (ρ x))
\end{code}

\begin{code}
renameE : ∀{Γ Δ K K'} → ⋆.Ren Γ Δ → EvalCxt Γ K K' → EvalCxt Δ K K'
renameE ρ •        = •
renameE ρ (E ·E t) = renameE ρ E ·E ⋆.rename ρ t

renameE[] : ∀{Γ Δ K K'}(ρ : ⋆.Ren Γ Δ)(E : EvalCxt Γ K K')(t : Γ ⊢⋆ K)
  → ⋆.rename ρ (E [ t ]E) ≡ renameE ρ E [ ⋆.rename ρ t ]E
renameE[] ρ •        t = refl
renameE[] ρ (E ·E u) t = cong (_· _) (renameE[] ρ E t)
\end{code}

\begin{code}
substE : ∀{Γ Δ K K'} → ⋆.Sub Γ Δ → EvalCxt Γ K K' → EvalCxt Δ K K'
substE ρ •        = •
substE ρ (E ·E t) = substE ρ E ·E ⋆.subst ρ t
\end{code}

\begin{code}
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
          ( trans (sym (⋆.subst-rename (⋆.ext ρ⋆)
                                      (⋆.subst-cons ` (⋆.rename ρ⋆ A))
                                      B))
                 (trans (⋆.subst-cong _ _ (⋆.rename-subst-cons ρ⋆ A) B)
                        (⋆.rename-subst (⋆.subst-cons ` A) ρ⋆ B) ) )
          (rename ρ⋆ ρ t ·⋆ ⋆.rename ρ⋆ A)
rename {Γ}{Δ} ρ⋆ ρ (wrap M E N) =
  substEq (λ A → Δ ⊢ A)
          (sym (renameE[] ρ⋆ E (μ M)))
          (wrap ((⋆.rename (⋆.ext ρ⋆) M))
                (renameE ρ⋆ E)
                (substEq (λ A → Δ ⊢ A)
                         (trans (renameE[] ρ⋆ E (M ⋆.[ μ M ]))
                                (cong (renameE ρ⋆ E [_]E)
                                      (trans (sym (⋆.rename-subst (⋆.subst-cons ` (μ M)) ρ⋆ M))
                                             (trans (⋆.subst-cong
                                                      _
                                                      _
                                                      (λ x → sym (⋆.rename-subst-cons _ _ x))
                                                      M)
                                                    (⋆.subst-rename
                                                      (⋆.ext ρ⋆)
                                                      (⋆.subst-cons ` (μ (⋆.rename (⋆.ext ρ⋆) M)))
                                                      M)))))
                         (rename ρ⋆ ρ N)))
rename {Γ}{Δ} ρ⋆ ρ (unwrap {S = A} E M) =
  substEq (λ A → Δ ⊢ A)
          (trans (cong (renameE ρ⋆ E [_]E)
                       (trans (sym (⋆.subst-rename _ _ A))
                              (trans (⋆.subst-cong _ _ (⋆.rename-subst-cons _ _) A)
                                     (⋆.rename-subst _ _ A))))
                 (sym (renameE[] ρ⋆ E (A ⋆.[ μ A ]))))
          (unwrap (renameE ρ⋆ E )
                  (substEq (λ A → Δ ⊢ A) (renameE[] ρ⋆ E (μ A)) (rename ρ⋆ ρ M)))
rename ρ⋆ ρ (conv p t) = conv (rename≡β ρ⋆ p) (rename ρ⋆ ρ t)
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
          (trans (sym (⋆.rename-subst σ⋆ S A))
                 (⋆.subst-rename S (⋆.exts σ⋆) A))
          (weaken⋆ (σ x))

\end{code}

\begin{code}
{-
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
          (trans (sym (⋆.subst-comp (⋆.exts σ⋆)
                                    (⋆.subst-cons ` (⋆.subst σ⋆ M))
                                    B))
                 (trans (⋆.subst-cong (⋆.subst (⋆.subst-cons ` (⋆.subst σ⋆ M))
                                     ∘
                                     ⋆.exts σ⋆)
                                    (⋆.subst σ⋆ ∘ ⋆.subst-cons ` M)
                                    (⋆.subst-subst-cons σ⋆ M)
                                    B)
                        (⋆.subst-comp (⋆.subst-cons ` M) σ⋆ B)))
          (subst σ⋆ σ L ·⋆ ⋆.subst σ⋆ M)
subst {Γ}{Δ} σ⋆ σ (wrap M N) =
  wrap (⋆.subst (⋆.exts σ⋆) M)
       (substEq (λ A → Δ ⊢ A)
                (trans (sym (⋆.subst-comp (⋆.subst-cons ` (μ M)) σ⋆ M))
                       (trans (⋆.subst-cong
                                _
                                _
                                (λ x → sym (⋆.subst-subst-cons _ _ x))
                                M)
                              (⋆.subst-comp
                                (⋆.exts σ⋆)
                                (⋆.subst-cons ` (μ (⋆.subst (⋆.exts σ⋆) M)))
                                M)))
                (subst σ⋆ σ N))
subst {Γ}{Δ} σ⋆ σ (unwrap {S = A} M) =
  substEq (λ A → Δ ⊢ A)
          (trans (trans (sym (⋆.subst-comp _ _ A))
                        (⋆.subst-cong _ _ (⋆.subst-subst-cons _ _) A))
                 (⋆.subst-comp _ _ A))
          (unwrap (subst σ⋆ σ M))
subst σ⋆ σ (conv p t) = conv (subst≡β σ⋆ p) (subst σ⋆ σ t)
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
                                     (⋆.subst-rename S (⋆.subst-cons ` A) A'))
                                     (` x)})
          t
-}
\end{code}
