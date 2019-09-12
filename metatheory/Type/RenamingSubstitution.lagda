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
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
  → ∀{K}{A A' : Φ ⊢⋆ K}
  → A ≡α A'
    -------------------------------
  → ren f A ≡α ren g A'
ren-cong p (var≡α refl) = var≡α (p _)
ren-cong p (⇒≡α q r)    = ⇒≡α (ren-cong p q) (ren-cong p r)
ren-cong p (Π≡α q)      = Π≡α (ren-cong (ext-cong p) q)
ren-cong p (ƛ≡α q)      = ƛ≡α (ren-cong (ext-cong p) q)
ren-cong p (·≡α q r)    = ·≡α (ren-cong p q) (ren-cong p r)
ren-cong p μ≡α          = μ≡α
ren-cong p con≡α        = con≡α
\end{code}

First functor law for ren

\begin{code}
ren-id : ∀{Φ J}
 → (t : Φ ⊢⋆ J)
   ---------------
 → ren id t ≡α t
ren-id (` α)       = var≡α refl
ren-id (Π x A)     = Π≡α (transα (ren-cong ext-id reflα) (ren-id A))
ren-id (A ⇒ B)     = ⇒≡α (ren-id A) (ren-id B)
ren-id (ƛ x A)     = ƛ≡α (transα (ren-cong ext-id reflα) (ren-id A))
ren-id (A · B)     = ·≡α (ren-id A) (ren-id B)
ren-id μ1          = μ≡α
ren-id (con tcn)   = con≡α
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
  → ren (f ∘ g) A ≡α ren f (ren g A)
ren-comp (` x)       = var≡α refl
ren-comp (Π x A)     =
  Π≡α (transα (ren-cong ext-comp reflα) (ren-comp A))
ren-comp (A ⇒ B)     = ⇒≡α (ren-comp A) (ren-comp B)
ren-comp (ƛ x A)     =
  ƛ≡α (transα (ren-cong ext-comp reflα) (ren-comp A))
ren-comp (A · B)     = ·≡α (ren-comp A) (ren-comp B)
ren-comp μ1          = μ≡α
ren-comp (con tcn)   = con≡α
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
  → exts ` x ≡α ` x 
exts-id Z     = reflα
exts-id (S x) = reflα
\end{code}

Congruence lemma for exts

\begin{code}
exts-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(α : Φ ∋⋆ J) → f α ≡α g α)
  → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
    -------------------------------
  → exts f α ≡α exts g α
exts-cong p Z     = var≡α refl
exts-cong p (S α) = ren-cong (λ _ → refl) (p α)
\end{code}

Congruence lemma for subst

\begin{code}
subst-cong : ∀ {Φ Ψ}
  → {f g : Sub Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡α g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------------
  → subst f A ≡α subst g A
subst-cong p (` x)       = p x
subst-cong p (Π x A)     = Π≡α (subst-cong (exts-cong p) A)
subst-cong p (A ⇒ B)     = ⇒≡α (subst-cong p A) (subst-cong p B)
subst-cong p (ƛ x A)     = ƛ≡α (subst-cong (exts-cong p) A)
subst-cong p (A · B)     = ·≡α (subst-cong p A) (subst-cong p B)
subst-cong p μ1          = μ≡α
subst-cong p (con tcn)   = con≡α
\end{code}

\begin{code}
subst-cong' : ∀ {Φ Ψ}
  → (f : Sub Φ Ψ)
  → ∀{K}{A A' : Φ ⊢⋆ K}
  → A ≡α A'
    -------------------------------
  → subst f A ≡α subst f A'
subst-cong' f (var≡α refl) = reflα
subst-cong' f (⇒≡α p q)    = ⇒≡α (subst-cong' f p) (subst-cong' f q)
subst-cong' f (Π≡α p)      = Π≡α (subst-cong' (exts f) p)
subst-cong' f (ƛ≡α p)      = ƛ≡α (subst-cong' (exts f) p)
subst-cong' f (·≡α p q)    = ·≡α (subst-cong' f p) (subst-cong' f q)
subst-cong' f μ≡α          = μ≡α
subst-cong' f con≡α        = con≡α
\end{code}

First relative monad law for subst

\begin{code}
subst-id : ∀ {Φ J}
  → (t : Φ ⊢⋆ J)
    -------------
  → subst ` t ≡α t
subst-id (` α)      = var≡α refl
subst-id (Π x A)    = Π≡α (transα (subst-cong exts-id A) (subst-id A))
subst-id (A ⇒ B)    = ⇒≡α (subst-id A) (subst-id B)
subst-id (ƛ x A)    = ƛ≡α (transα (subst-cong exts-id A) (subst-id A))
subst-id (A · B)    = ·≡α (subst-id A) (subst-id B)
subst-id μ1         = μ≡α
subst-id (con tcn)  = con≡α
\end{code}

Fusion of exts and ext

\begin{code}
exts-ext : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------
  → exts (f ∘ g) x ≡α exts f (ext g x)
exts-ext Z     = reflα
exts-ext (S x) = reflα
\end{code}

Fusion for subst and ren

\begin{code}
subst-ren : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    --------------------------------------
  → subst (f ∘ g) A ≡α subst f (ren g A)
subst-ren (` α)       = reflα
subst-ren (Π x A)     =
  Π≡α (transα (subst-cong exts-ext A) (subst-ren A))
subst-ren (A ⇒ B)     = ⇒≡α (subst-ren A) (subst-ren B)
subst-ren (ƛ x A)     =
  ƛ≡α (transα (subst-cong exts-ext A) (subst-ren A))
subst-ren (A · B)     = ·≡α (subst-ren A) (subst-ren B)
subst-ren μ1          = μ≡α
subst-ren (con tcn)   = con≡α
\end{code}

Fusion for exts and ext

\begin{code}
ren-ext-exts : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -------------------------------------------------
  → exts (ren f ∘ g) x ≡α ren (ext f) (exts g x)
ren-ext-exts Z     = var≡α refl
ren-ext-exts (S x) = transα (symα (ren-comp _)) (ren-comp _)
\end{code}

Fusion for ren and subst

\begin{code}
ren-subst : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    ---------------------------------------------
  → subst (ren f ∘ g) A ≡α ren f (subst g A)
ren-subst (` α)       = ren-cong (λ _ → refl) reflα
ren-subst (Π x A)     =
  Π≡α (transα (subst-cong ren-ext-exts  A) (ren-subst A))
ren-subst (A ⇒ B)     = ⇒≡α (ren-subst A) (ren-subst B)
ren-subst (ƛ x A)     =
  ƛ≡α (transα (subst-cong ren-ext-exts A) (ren-subst A))
ren-subst (A · B)     = ·≡α (ren-subst A) (ren-subst B)
ren-subst μ1          = μ≡α
ren-subst (con tcn)   = con≡α
\end{code}

Fusion of two exts

\begin{code}
extscomp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------------------
  → exts (subst f ∘ g) x ≡α subst (exts f) (exts g x)
extscomp         Z     = var≡α refl
extscomp {g = g} (S x) = transα (symα (ren-subst (g x))) (subst-ren (g x))
\end{code}

Fusion of substitutions/third relative monad law for subst

\begin{code}
subst-comp : ∀{Φ Ψ Θ}
  → {g : Sub Φ Ψ}
  → {f : Sub Ψ Θ}
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------
  → subst (subst f ∘ g) A ≡α subst f (subst g A)
subst-comp (` x)       = reflα
subst-comp (Π x A)     = Π≡α (transα (subst-cong extscomp A) (subst-comp A))
subst-comp (A ⇒ B)     = ⇒≡α (subst-comp A) (subst-comp B)
subst-comp (ƛ x A)     = ƛ≡α (transα (subst-cong extscomp A) (subst-comp A))
subst-comp (A · B)     = ·≡α (subst-comp A) (subst-comp B)
subst-comp μ1          = μ≡α
subst-comp (con tcn)   = con≡α
\end{code}

Commuting subst-cons and ren

\begin{code}
ren-subst-cons : ∀{Γ Δ}{J K} 
  → (ρ : Ren Γ Δ)
  → (A : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    -----------------------------------------------------------------
  → subst-cons ` (ren ρ A) (ext ρ x) ≡α ren ρ (subst-cons ` A x)
ren-subst-cons ρ A Z     = reflα
ren-subst-cons ρ A (S x) = reflα
\end{code}

Commuting subst-cons and subst

\begin{code}
subst-subst-cons : ∀{Γ Δ}{J K} 
  → (σ : Sub Γ Δ)
  → (M : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    ------------------------------------------------------------------------
  → subst (subst-cons ` (subst σ M)) (exts σ x) ≡α subst σ (subst-cons ` M x)
subst-subst-cons σ M Z     = reflα
subst-subst-cons σ M (S x) = transα (symα (subst-ren (σ x))) (subst-id (σ x))
\end{code}
