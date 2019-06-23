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
ren : ∀ {Φ Ψ}
  → Ren Φ Ψ
    -----------------------
  → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
ren ρ (` α)       = ` (ρ α)
ren ρ (Π x B)     = Π x (ren (ext ρ) B)
ren ρ (A ⇒ B)     = ren ρ A ⇒ ren ρ B
ren ρ (ƛ x B)     = ƛ x (ren (ext ρ) B)
ren ρ (A · B)     = ren ρ A · ren ρ B
ren ρ μ1          = μ1
ren ρ (con tcn) = con tcn
\end{code}

Weakening is a special case of renaming.

\begin{code}
weaken : ∀ {Φ J K}
  → Φ ⊢⋆ J
    -----------
  → Φ ,⋆ K ⊢⋆ J
weaken = ren S
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

This congruence lemma and analogous ones for exts⋆, ren, and
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
ren-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → ren f A ≡ ren g A
ren-cong p (` x)       = cong ` (p x)
ren-cong p (Π x A)     = cong (Π x) (ren-cong (ext-cong p) A)
ren-cong p (A ⇒ B)     = cong₂ _⇒_ (ren-cong p A) (ren-cong p B)
ren-cong p (ƛ x A)     = cong (ƛ x) (ren-cong (ext-cong p) A)
ren-cong p (A · B)     = cong₂ _·_ (ren-cong p A) (ren-cong p B)
ren-cong p μ1          = refl
ren-cong p (con tcn)   = refl
\end{code}

First functor law for ren

\begin{code}
ren-id : ∀{Φ J}
 → (t : Φ ⊢⋆ J)
   ---------------
 → ren id t ≡ t
ren-id (` x)       = refl
ren-id (Π x t)     = cong (Π x) (trans (ren-cong ext-id t) (ren-id t))
ren-id (t ⇒ u)     = cong₂ _⇒_ (ren-id t) (ren-id u)
ren-id (ƛ x t)     = cong (ƛ x) (trans (ren-cong ext-id t) (ren-id t))
ren-id (t · u)     = cong₂ _·_ (ren-id t) (ren-id u)
ren-id μ1          = refl
ren-id (con tcn)   = refl
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

Second functor law for ren

\begin{code}
ren-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ----------------------------------------
  → ren (f ∘ g) A ≡ ren f (ren g A)
ren-comp (` x)       = refl
ren-comp (Π x A)       =
  cong (Π x) (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A ⇒ B)     = cong₂ _⇒_ (ren-comp A) (ren-comp B)
ren-comp (ƛ x A)     =
  cong (ƛ x) (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A · B)     = cong₂ _·_ (ren-comp A) (ren-comp B)
ren-comp μ1          = refl
ren-comp (con tcn)   = refl
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

Fusion for subst and ren

\begin{code}
subst-ren : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    --------------------------------------
  → subst (f ∘ g) A ≡ subst f (ren g A)
subst-ren (` x)       = refl
subst-ren (Π x A)     =
  cong (Π x) (trans (subst-cong exts-ext A) (subst-ren A))
subst-ren (A ⇒ B)     = cong₂ _⇒_ (subst-ren A) (subst-ren B)
subst-ren (ƛ x A)     =
  cong (ƛ x) (trans (subst-cong exts-ext A) (subst-ren A))
subst-ren (A · B)     = cong₂ _·_ (subst-ren A) (subst-ren B)
subst-ren μ1           = refl
subst-ren (con tcn)   = refl
\end{code}

Fusion for exts and ext

\begin{code}
ren-ext-exts : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -------------------------------------------------
  → exts (ren f ∘ g) x ≡ ren (ext f) (exts g x)
ren-ext-exts Z     = refl
ren-ext-exts (S x) = trans (sym (ren-comp _)) (ren-comp _)
\end{code}

Fusion for ren and subst

\begin{code}
ren-subst : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ---------------------------------------------
  → subst (ren f ∘ g) A ≡ ren f (subst g A)
ren-subst (` x)       = refl
ren-subst (Π x A)     =
  cong (Π x) (trans (subst-cong ren-ext-exts A) (ren-subst A))
ren-subst (A ⇒ B)     = cong₂ _⇒_ (ren-subst A) (ren-subst B)
ren-subst (ƛ x A)     =
  cong (ƛ x) (trans (subst-cong ren-ext-exts A) (ren-subst A))
ren-subst (A · B)     = cong₂ _·_ (ren-subst A) (ren-subst B)
ren-subst μ1          = refl
ren-subst (con tcn)   = refl
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
extscomp {g = g} (S x) = trans (sym (ren-subst (g x))) (subst-ren (g x))
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

Commuting subst-cons and ren

\begin{code}
ren-subst-cons : ∀{Γ Δ}{J K} 
  → (ρ : Ren Γ Δ)
  → (A : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    -----------------------------------------------------------------
  → subst-cons ` (ren ρ A) (ext ρ x) ≡ ren ρ (subst-cons ` A x)
ren-subst-cons ρ A Z     = refl
ren-subst-cons ρ A (S x) = refl
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
subst-subst-cons σ M (S x) = trans (sym (subst-ren (σ x))) (subst-id (σ x))
\end{code}
