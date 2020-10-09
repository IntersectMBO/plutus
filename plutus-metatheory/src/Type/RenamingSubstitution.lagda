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
ren ρ (Π B)       = Π (ren (ext ρ) B)
ren ρ (A ⇒ B)     = ren ρ A ⇒ ren ρ B
ren ρ (ƛ B)       = ƛ (ren (ext ρ) B)
ren ρ (A · B)     = ren ρ A · ren ρ B
ren ρ (μ A B)     = μ (ren ρ A) (ren ρ B)
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
  → (α : Φ ,⋆ K ∋⋆ J)
    ----------------
  → ext id α ≡ α
ext-id Z     = refl
ext-id (S α) = refl
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
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
  → ∀{J K}(α : Φ ,⋆ J ∋⋆ K)
    -------------------------------
  → ext f α ≡ ext g α
ext-cong p Z     = refl
ext-cong p (S α) = cong S (p α)
\end{code}

Congruence lemma for renaming⋆

\begin{code}
ren-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → ren f A ≡ ren g A
ren-cong p (` α)   = cong ` (p α)
ren-cong p (Π A)   = cong Π (ren-cong (ext-cong p) A)
ren-cong p (A ⇒ B) = cong₂ _⇒_ (ren-cong p A) (ren-cong p B)
ren-cong p (ƛ A)   = cong ƛ (ren-cong (ext-cong p) A)
ren-cong p (A · B) = cong₂ _·_ (ren-cong p A) (ren-cong p B)
ren-cong p (μ A B) = cong₂ μ (ren-cong p A) (ren-cong p B)
ren-cong p (con c) = refl
\end{code}

First functor law for ren

\begin{code}
ren-id : ∀{Φ J}
 → (t : Φ ⊢⋆ J)
   ---------------
 → ren id t ≡ t
ren-id (` α)     = refl
ren-id (Π A)     = cong Π (trans (ren-cong ext-id A) (ren-id A))
ren-id (A ⇒ B)   = cong₂ _⇒_(ren-id A) (ren-id B)
ren-id (ƛ A)     = cong ƛ (trans (ren-cong ext-id A) (ren-id A))
ren-id (A · B)   = cong₂ _·_ (ren-id A) (ren-id B)
ren-id (μ A B)   = cong₂ μ (ren-id A) (ren-id B)
ren-id (con tcn) = refl
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
ren-comp (Π A)     =
  cong Π (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A ⇒ B)     = cong₂ _⇒_ (ren-comp A) (ren-comp B)
ren-comp (ƛ A)       =
  cong ƛ (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A · B)     = cong₂ _·_ (ren-comp A) (ren-comp B)
ren-comp (μ A B)     = cong₂ μ (ren-comp A) (ren-comp B)
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
subst σ (Π B)       = Π (subst (exts σ) B)
subst σ (A ⇒ B)     = subst σ A ⇒ subst σ B
subst σ (ƛ B)       = ƛ (subst (exts σ) B)
subst σ (A · B)     = subst σ A · subst σ B
subst σ (μ A B)     = μ (subst σ A) (subst σ B)
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
  → (α : Φ ,⋆ K ∋⋆ J)
    -----------------
  → exts ` α ≡ ` α 
exts-id Z     = refl
exts-id (S α) = refl
\end{code}

Congruence lemma for exts

\begin{code}
exts-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
  → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
    -------------------------------
  → exts f α ≡ exts g α
exts-cong p Z     = refl
exts-cong p (S α) = cong (ren S) (p α)
\end{code}

Congruence lemma for subst

\begin{code}
subst-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → subst f A ≡ subst g A
subst-cong p (` α)       = p α
subst-cong p (Π A)       = cong Π (subst-cong (exts-cong p) A)
subst-cong p (A ⇒ B)     = cong₂ _⇒_ (subst-cong p A) (subst-cong p B)
subst-cong p (ƛ A)       = cong ƛ (subst-cong (exts-cong p) A)
subst-cong p (A · B)     = cong₂ _·_ (subst-cong p A) (subst-cong p B)
subst-cong p (μ A B)     = cong₂ μ (subst-cong p A) (subst-cong p B)
subst-cong p (con tcn)   = refl
\end{code}

First relative monad law for subst

\begin{code}
subst-id : ∀ {Φ J}
  → (t : Φ ⊢⋆ J)
    -------------
  → subst ` t ≡ t
subst-id (` α)      = refl
subst-id (Π A)      = cong Π (trans (subst-cong exts-id A) (subst-id A))
subst-id (A ⇒ B)    = cong₂ _⇒_ (subst-id A) (subst-id B)
subst-id (ƛ A)      = cong ƛ (trans (subst-cong exts-id A) (subst-id A))
subst-id (A · B)    = cong₂ _·_ (subst-id A) (subst-id B)
subst-id (μ A B)    = cong₂ μ (subst-id A) (subst-id B)
subst-id (con tcn)  = refl
\end{code}

Fusion of exts and ext

\begin{code}
exts-ext : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
    ------------------------------------
  → exts (f ∘ g) α ≡ exts f (ext g α)
exts-ext Z     = refl
exts-ext (S α) = refl
\end{code}

Fusion for subst and ren

\begin{code}
subst-ren : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    --------------------------------------
  → subst (f ∘ g) A ≡ subst f (ren g A)
subst-ren (` α)     = refl
subst-ren (Π A)     =
  cong Π (trans (subst-cong exts-ext A) (subst-ren A))
subst-ren (A ⇒ B)   = cong₂ _⇒_ (subst-ren A) (subst-ren B)
subst-ren (ƛ A)     =
  cong ƛ (trans (subst-cong exts-ext A) (subst-ren A))
subst-ren (A · B)   = cong₂ _·_ (subst-ren A) (subst-ren B)
subst-ren (μ A B)   = cong₂ μ (subst-ren A) (subst-ren B)
subst-ren (con tcn) = refl
\end{code}

Fusion for exts and ext

\begin{code}
ren-ext-exts : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
    -------------------------------------------------
  → exts (ren f ∘ g) α ≡ ren (ext f) (exts g α)
ren-ext-exts Z     = refl
ren-ext-exts (S α) = trans (sym (ren-comp _)) (ren-comp _)
\end{code}

Fusion for ren and subst

\begin{code}
ren-subst : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ---------------------------------------------
  → subst (ren f ∘ g) A ≡ ren f (subst g A)
ren-subst (` α)     = refl
ren-subst (Π A)     =
  cong Π (trans (subst-cong ren-ext-exts  A) (ren-subst A))
ren-subst (A ⇒ B)   = cong₂ _⇒_ (ren-subst A) (ren-subst B)
ren-subst (ƛ A)     =
  cong ƛ (trans (subst-cong ren-ext-exts A) (ren-subst A))
ren-subst (A · B)   = cong₂ _·_ (ren-subst A) (ren-subst B)
ren-subst (μ A B)   = cong₂ μ (ren-subst A) (ren-subst B)
ren-subst (con tcn) = refl
\end{code}

Fusion of two exts

\begin{code}
extscomp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
    ------------------------------------------------
  → exts (subst f ∘ g) α ≡ subst (exts f) (exts g α)
extscomp         Z     = refl
extscomp {g = g} (S α) = trans (sym (ren-subst (g α))) (subst-ren (g α))
\end{code}

Fusion of substitutions/third relative monad law for subst

\begin{code}
subst-comp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------
  → subst (subst f ∘ g) A ≡ subst f (subst g A)
subst-comp (` x)     = refl
subst-comp (Π A)     = cong Π (trans (subst-cong extscomp A) (subst-comp A))
subst-comp (A ⇒ B)   = cong₂ _⇒_ (subst-comp A) (subst-comp B)
subst-comp (ƛ A)     = cong ƛ (trans (subst-cong extscomp A) (subst-comp A))
subst-comp (A · B)   = cong₂ _·_ (subst-comp A) (subst-comp B)
subst-comp (μ A B)   = cong₂ μ (subst-comp A) (subst-comp B)
subst-comp (con tcn) = refl
\end{code}

Commuting subst-cons and ren

\begin{code}
ren-subst-cons : ∀{Φ Ψ}{J K} 
  → (ρ : Ren Φ Ψ)
  → (A : Φ ⊢⋆ K)
  → (α : Φ ,⋆ K ∋⋆ J)
    -----------------------------------------------------------------
  → subst-cons ` (ren ρ A) (ext ρ α) ≡ ren ρ (subst-cons ` A α)
ren-subst-cons ρ A Z     = refl
ren-subst-cons ρ A (S α) = refl
\end{code}

Commuting subst-cons and subst

\begin{code}
subst-subst-cons : ∀{Φ Ψ}{J K} 
  → (σ : Sub Φ Ψ)
  → (M : Φ ⊢⋆ K)
  → (α : Φ ,⋆ K ∋⋆ J)
    ------------------------------------------------------------------------
  → subst (subst-cons ` (subst σ M)) (exts σ α) ≡ subst σ (subst-cons ` M α)
subst-subst-cons σ M Z     = refl
subst-subst-cons σ M (S α) = trans (sym (subst-ren (σ α))) (subst-id (σ α))
\end{code}

A useful lemma for fixing up the types when renaming a wrap or unwrap

\begin{code}
ren-μ : ∀{Φ Ψ}{K}(ρ⋆ : Ren Φ Ψ)(A : Φ ⊢⋆ _)(B : Φ ⊢⋆ K) →
  ren ρ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
  ≡
  ren ρ⋆ A · ƛ (μ (weaken (ren ρ⋆ A)) (` Z)) · ren ρ⋆ B
ren-μ ρ⋆ A B = cong
  (λ X → ren ρ⋆ A · ƛ (μ X (` Z)) · ren ρ⋆ B)
  (trans (sym (ren-comp A)) (ren-comp A))
\end{code}


A useful lemma for fixing up the types when substituting into a wrap or unwrap

\begin{code}
subst-μ : ∀{Φ Ψ}{K}(σ⋆ : Sub Φ Ψ)(A : Φ ⊢⋆ _)(B : Φ ⊢⋆ K) →
  subst σ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
  ≡
  subst σ⋆ A · ƛ (μ (weaken (subst σ⋆ A)) (` Z)) · subst σ⋆ B
subst-μ σ⋆ A B = cong
  (λ X → subst σ⋆ A · ƛ (μ X (` Z)) · subst σ⋆ B)
  (trans (sym (subst-ren A)) (ren-subst A))
\end{code}
