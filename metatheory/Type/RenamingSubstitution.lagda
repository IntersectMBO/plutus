\begin{code}
module Type.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Type

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
\end{code}

## Type renaming

A type renaming is a mapping of type variables to type variables.

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J
\end{code}

Let `ρ` range of renamings.

Extending a type renaming — used when going under a binder.

\begin{code}
ext : ∀ {Φ Ψ} → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ------------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ∋⋆ J)
ext ρ Z      =  Z
ext ρ (S α)  =  S (ρ α)
\end{code}

Apply a type renaming to a type.
\begin{code}
rename : ∀ {Φ Ψ}
  → Ren Φ Ψ
    -----------------------
  → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
rename ρ (` α)       = ` (ρ α)
rename ρ (Π x B)     = Π x (rename (ext ρ) B)
rename ρ (A ⇒ B)     = rename ρ A ⇒ rename ρ B
rename ρ (ƛ x B)     = ƛ x (rename (ext ρ) B)
rename ρ (A · B)     = rename ρ A · rename ρ B
rename ρ μ1          = μ1
rename ρ (con tcn) = con tcn
\end{code}

Weakening is a special case of renaming.

\begin{code}
weaken : ∀ {Φ J K}
  → Φ ⊢⋆ J
    -----------
  → Φ ,⋆ K ⊢⋆ J
weaken = rename S
\end{code}

## Renaming proofs

First functor law for ext

\begin{code}
ext-id :  ∀ {Φ J K}
  → (x : Φ ,⋆ K ∋⋆ J)
    ----------------
  → ext id x ≡ x
ext-id Z     = refl
ext-id (S x) = refl
\end{code}

This congruence lemma and analogous ones for exts⋆, rename, and
subst⋆ avoids the use of extensionality when reasoning about equal
renamings/substitutions as we only need a pointwise version of
equality. If we used the standard library's cong we would need to
postulate extensionality and our equality proofs wouldn't compute. I
learnt this from Conor McBride.

\begin{code}
ext-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ J ∋⋆ K)
    -------------------------------
  → ext f x ≡ ext g x
ext-cong p Z     = refl
ext-cong p (S x) = cong S (p x)
\end{code}

Congruence lemma for renaming⋆

\begin{code}
rename-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → rename f A ≡ rename g A
rename-cong p (` x)       = cong ` (p x)
rename-cong p (Π x A)     = cong (Π x) (rename-cong (ext-cong p) A)
rename-cong p (A ⇒ B)     = cong₂ _⇒_ (rename-cong p A) (rename-cong p B)
rename-cong p (ƛ x A)     = cong (ƛ x) (rename-cong (ext-cong p) A)
rename-cong p (A · B)     = cong₂ _·_ (rename-cong p A) (rename-cong p B)
rename-cong p μ1          = refl
rename-cong p (con tcn)   = refl
\end{code}

First functor law for rename

\begin{code}
rename-id : ∀{Φ J}
 → (t : Φ ⊢⋆ J)
   ---------------
 → rename id t ≡ t
rename-id (` x)       = refl
rename-id (Π x t)     = cong (Π x) (trans (rename-cong ext-id t) (rename-id t))
rename-id (t ⇒ u)     = cong₂ _⇒_ (rename-id t) (rename-id u)
rename-id (ƛ x t)     = cong (ƛ x) (trans (rename-cong ext-id t) (rename-id t))
rename-id (t · u)     = cong₂ _·_ (rename-id t) (rename-id u)
rename-id μ1          = refl
rename-id (con tcn)   = refl
\end{code}

Second functor law for ext

\begin{code}
ext-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -------------------------------
  → ext (f ∘ g) x ≡ ext f (ext g x)
ext-comp Z     = refl
ext-comp (S x) = refl
\end{code}

Second functor law for rename

\begin{code}
rename-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ----------------------------------------
  → rename (f ∘ g) A ≡ rename f (rename g A)
rename-comp (` x)       = refl
rename-comp (Π x A)       =
  cong (Π x) (trans (rename-cong ext-comp A) (rename-comp A))
rename-comp (A ⇒ B)     = cong₂ _⇒_ (rename-comp A) (rename-comp B)
rename-comp (ƛ x A)     =
  cong (ƛ x) (trans (rename-cong ext-comp A) (rename-comp A))
rename-comp (A · B)     = cong₂ _·_ (rename-comp A) (rename-comp B)
rename-comp μ1          = refl
rename-comp (con tcn)   = refl
\end{code}

## Type substitution

A type substitution is a mapping of type variables to types.

\begin{code}
Sub : Ctx⋆ → Ctx⋆ → Set
Sub Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J
\end{code}

Let `σ` range over substitutions.

Extending a type substitution — used when going under a binder.

\begin{code}
exts : ∀ {Φ Ψ}
  → Sub Φ Ψ
    -------------------------------
  → (∀ {K} → Sub (Φ ,⋆ K) (Ψ ,⋆ K))
exts σ Z      = ` Z
exts σ (S α)  = weaken (σ α)
\end{code}

Apply a type substitution to a type.

\begin{code}
subst : ∀ {Φ Ψ}
  → Sub Φ Ψ
    -------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
subst σ (` α)       = σ α
subst σ (Π x B)     = Π x (subst (exts σ) B)
subst σ (A ⇒ B)     = subst σ A ⇒ subst σ B
subst σ (ƛ x B)     = ƛ x (subst (exts σ) B)
subst σ (A · B)     = subst σ A · subst σ B
subst σ μ1           = μ1
subst σ (con tcn)   = con tcn
\end{code}

Extend a substitution with an additional type (analogous to cons for
backward lists)

\begin{code}
subst-cons : ∀{Φ Ψ}
  → Sub Φ Ψ
  → ∀{J}(A : Ψ ⊢⋆ J)
    ----------------
  → Sub (Φ ,⋆ J) Ψ
subst-cons f A Z = A
subst-cons f A (S x) = f x
\end{code}

A special case is substitution a type for the outermost free variable.

\begin{code}
_[_] : ∀ {Φ J K}
  → Φ ,⋆ K ⊢⋆ J
  → Φ ⊢⋆ K 
    ------------
  → Φ ⊢⋆ J
B [ A ] =  subst (subst-cons ` A) B
\end{code}

## Type Substitution Proofs

Extending the identity substitution yields the identity substitution

\begin{code}
exts-id : ∀ {Φ J K}
  → (x : Φ ,⋆ K ∋⋆ J)
    -----------------
  → exts ` x ≡ ` x 
exts-id Z     = refl
exts-id (S x) = refl
\end{code}

Congruence lemma for exts

\begin{code}
exts-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -------------------------------
  → exts f x ≡ exts g x
exts-cong p Z     = refl
exts-cong p (S x) = cong weaken (p x)
\end{code}

Congruence lemma for subst

\begin{code}
subst-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → subst f A ≡ subst g A
subst-cong p (` x)       = p x
subst-cong p (Π x A)     = cong (Π x) (subst-cong (exts-cong p) A)
subst-cong p (A ⇒ B)     = cong₂ _⇒_ (subst-cong p A) (subst-cong p B)
subst-cong p (ƛ x A)     = cong (ƛ x) (subst-cong (exts-cong p) A)
subst-cong p (A · B)     = cong₂ _·_ (subst-cong p A) (subst-cong p B)
subst-cong p μ1          = refl
subst-cong p (con tcn)   = refl
\end{code}

First relative monad law for subst

\begin{code}
subst-id : ∀ {Φ J}
  → (t : Φ ⊢⋆ J)
    -------------
  → subst ` t ≡ t
subst-id (` x)      = refl
subst-id (Π x A)    = cong (Π x) (trans (subst-cong exts-id A) (subst-id A))
subst-id (A ⇒ B)    = cong₂ _⇒_ (subst-id A) (subst-id B)
subst-id (ƛ x A)     = cong (ƛ x) (trans (subst-cong exts-id A) (subst-id A))
subst-id (A · B)     = cong₂ _·_ (subst-id A) (subst-id B)
subst-id μ1          = refl
subst-id (con tcn)   = refl
\end{code}

Fusion of exts and ext

\begin{code}
exts-ext : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------
  → exts (f ∘ g) x ≡ exts f (ext g x)
exts-ext Z     = refl
exts-ext (S x) = refl
\end{code}

Fusion for subst and rename

\begin{code}
subst-rename : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    --------------------------------------
  → subst (f ∘ g) A ≡ subst f (rename g A)
subst-rename (` x)       = refl
subst-rename (Π x A)     =
  cong (Π x) (trans (subst-cong exts-ext A) (subst-rename A))
subst-rename (A ⇒ B)     = cong₂ _⇒_ (subst-rename A) (subst-rename B)
subst-rename (ƛ x A)     =
  cong (ƛ x) (trans (subst-cong exts-ext A) (subst-rename A))
subst-rename (A · B)     = cong₂ _·_ (subst-rename A) (subst-rename B)
subst-rename μ1           = refl
subst-rename (con tcn)   = refl
\end{code}

Fusion for exts and ext

\begin{code}
rename-ext-exts : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -------------------------------------------------
  → exts (rename f ∘ g) x ≡ rename (ext f) (exts g x)
rename-ext-exts Z     = refl
rename-ext-exts (S x) = trans (sym (rename-comp _)) (rename-comp _)
\end{code}

Fusion for rename and subst

\begin{code}
rename-subst : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ---------------------------------------------
  → subst (rename f ∘ g) A ≡ rename f (subst g A)
rename-subst (` x)       = refl
rename-subst (Π x A)     =
  cong (Π x) (trans (subst-cong rename-ext-exts A) (rename-subst A))
rename-subst (A ⇒ B)     = cong₂ _⇒_ (rename-subst A) (rename-subst B)
rename-subst (ƛ x A)     =
  cong (ƛ x) (trans (subst-cong rename-ext-exts A) (rename-subst A))
rename-subst (A · B)     = cong₂ _·_ (rename-subst A) (rename-subst B)
rename-subst μ1          = refl
rename-subst (con tcn)   = refl
\end{code}

Fusion of two exts

\begin{code}
extscomp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------------------
  → exts (subst f ∘ g) x ≡ subst (exts f) (exts g x)
extscomp         Z     = refl
extscomp {g = g} (S x) = trans (sym (rename-subst (g x))) (subst-rename (g x))
\end{code}

Fusion of substitutions/third relative monad law for subst

\begin{code}
subst-comp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------
  → subst (subst f ∘ g) A ≡ subst f (subst g A)
subst-comp (` x)       = refl
subst-comp (Π x A)     = cong (Π x) (trans (subst-cong extscomp A) (subst-comp A))
subst-comp (A ⇒ B)     = cong₂ _⇒_ (subst-comp A) (subst-comp B)
subst-comp (ƛ x A)     = cong (ƛ x) (trans (subst-cong extscomp A) (subst-comp A))
subst-comp (A · B)     = cong₂ _·_ (subst-comp A) (subst-comp B)
subst-comp μ1          = refl
subst-comp (con tcn)   = refl
\end{code}

Commuting subst-cons and rename

\begin{code}
rename-subst-cons : ∀{Γ Δ}{J K} 
  → (ρ : Ren Γ Δ)
  → (A : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    -----------------------------------------------------------------
  → subst-cons ` (rename ρ A) (ext ρ x) ≡ rename ρ (subst-cons ` A x)
rename-subst-cons ρ A Z     = refl
rename-subst-cons ρ A (S x) = refl
\end{code}

Commuting subst-cons and subst

\begin{code}
subst-subst-cons : ∀{Γ Δ}{J K} 
  → (σ : Sub Γ Δ)
  → (M : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    ------------------------------------------------------------------------
  → subst (subst-cons ` (subst σ M)) (exts σ x) ≡ subst σ (subst-cons ` M x)
subst-subst-cons σ M Z     = refl
subst-subst-cons σ M (S x) = trans (sym (subst-rename (σ x))) (subst-id (σ x))
\end{code}
