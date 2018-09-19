\begin{code}
module Type.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Type
\end{code}

Let `A`, `B`, `C` range over types.

## Type renaming

A type renaming is a mapping of type variables to type variables.

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
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
rename ρ (` α)    =  ` (ρ α)
rename ρ (Π B)    =  Π (rename (ext ρ) B)
rename ρ (A ⇒ B)  =  rename ρ A ⇒ rename ρ B
rename ρ (ƛ B)    = ƛ (rename (ext ρ) B)
rename ρ (A · B)  = rename ρ A · rename ρ B
rename ρ (μ B)    =  μ (rename (ext ρ) B)
\end{code}

Weakening is a special case of renaming.
\begin{code}
weaken : ∀ {Φ J K}
  → Φ ⊢⋆ J
    -------------
  → Φ ,⋆ K ⊢⋆ J
weaken = rename S
\end{code}

## Renaming proofs

First functor law for ext
\begin{code}
ext-id :  ∀ {Φ J K} → (x : Φ ,⋆ K ∋⋆ J) → ext id x ≡ x
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
ext-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ J ∋⋆ K)
    -------------------
  → ext f x ≡ ext g x
ext-cong f g p Z     = refl
ext-cong f g p (S x) = cong S (p x)
\end{code}
Congruence lemma for renaming⋆
\begin{code}
rename-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------
  → rename f A ≡ rename g A
rename-cong f g p (` x)   = cong ` (p x)
rename-cong f g p (Π A)   =
  cong Π (rename-cong (ext f) (ext g) (ext-cong f g p) A)
rename-cong f g p (A ⇒ B) =
  cong₂ _⇒_ (rename-cong f g p A) (rename-cong f g p B)
rename-cong f g p (ƛ A)   =
  cong ƛ (rename-cong (ext f) (ext g) (ext-cong f g p) A)
rename-cong f g p (A · B) =
  cong₂ _·_ (rename-cong f g p A) (rename-cong f g p B)
rename-cong f g p (μ A)   =
  cong μ (rename-cong (ext f) (ext g) (ext-cong f g p) A)
\end{code}

First functor law for rename
\begin{code}
rename-id : ∀{Φ J}(t : Φ ⊢⋆ J) → rename id t ≡ t
rename-id (` x)   = refl
rename-id (Π t)   =
  cong Π (trans (rename-cong (ext id) id ext-id t) (rename-id t))
rename-id (t ⇒ u) = cong₂ _⇒_ (rename-id t) (rename-id u)
rename-id (ƛ t)   =
  cong ƛ (trans (rename-cong (ext id) id ext-id t) (rename-id t))
rename-id (t · u) = cong₂ _·_ (rename-id t) (rename-id u)
rename-id (μ t)   =
  cong μ (trans (rename-cong (ext id) id ext-id t) (rename-id t))

\end{code}

Second functor law for ext
\begin{code}
ext-comp : ∀{Φ Ψ Θ}(g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ----------------------------------
  → ext (f ∘ g) x ≡ ext f (ext g x)
ext-comp g f Z     = refl
ext-comp g f (S x) = refl
\end{code}

Second functor law for renaming⋆
\begin{code}
rename-comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------
  → rename (f ∘ g) A ≡ rename f (rename g A)
rename-comp g f (` x)   = refl
rename-comp g f (Π A)   =
  cong Π
       (trans (rename-cong (ext (f ∘ g)) (ext f ∘ ext g) (ext-comp g f) A)
              (rename-comp (ext g) (ext f) A))
rename-comp g f (A ⇒ B) = cong₂ _⇒_ (rename-comp g f A) (rename-comp g f B)
rename-comp g f (ƛ A) = 
  cong ƛ
       (trans (rename-cong (ext (f ∘ g)) (ext f ∘ ext g) (ext-comp g f) A)
              (rename-comp (ext g) (ext f) A))
rename-comp g f (A · B) = cong₂ _·_ (rename-comp g f A) (rename-comp g f B)
rename-comp g f (μ A)   =
  cong μ
       (trans (rename-cong (ext (f ∘ g)) (ext f ∘ ext g) (ext-comp g f) A)
              (rename-comp (ext g) (ext f) A))
\end{code}
## Type substitution

A type substitution is a mapping of type variables to types.

Extending a type substitution — used when going under a binder.
\begin{code}
exts : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢⋆ J)
exts σ Z      =  ` Z
exts σ (S α)  =  weaken (σ α)
\end{code}

Apply a type substitution to a type.
\begin{code}
subst : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
subst σ (` α)     =  σ α
subst σ (Π B)     =  Π (subst (exts σ) B)
subst σ (A ⇒ B)   =  subst σ A ⇒ subst σ B
subst σ (ƛ B)     =  ƛ (subst (exts σ) B)
subst σ (A · B)   =  subst σ A · subst σ B
subst σ (μ B)     =  μ (subst (exts σ) B)
\end{code}

Extend a substitution with an additional type (analogous to cons for
backward lists)
\begin{code}
subst-cons : ∀{Φ Ψ} → (∀{K} → Φ ∋⋆ K → Ψ ⊢⋆ K) → ∀{J}(A : Ψ ⊢⋆ J) →
             (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢⋆ K)
subst-cons f A Z = A
subst-cons f A (S x) = f x
\end{code}

A special case is substitution a type for the outermost free variable.
\begin{code}
_[_] : ∀ {Φ J K}
        → Φ ,⋆ K ⊢⋆ J
        → Φ ⊢⋆ K 
          ------
        → Φ ⊢⋆ J
_[_] {Φ} {J} {K} B A =  subst (subst-cons ` A) B
\end{code}

## Type Substitution Proofs

Extending the identity substitution yields the identity substitution
\begin{code}
exts-id : ∀ {Φ J K}(x : Φ ,⋆ K ∋⋆ J)
    ----------------
  → exts ` x ≡ ` x 
exts-id Z     = refl
exts-id (S x) = refl
\end{code}

Congruence lemma for exts
\begin{code}
exts-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -----------------------
  → exts f x ≡ exts g x
exts-cong f g p Z     = refl
exts-cong f g p (S x) = cong weaken (p x)
\end{code}

Congruence lemma for subst
\begin{code}
subst-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -----------------------
  → subst f A ≡ subst g A
subst-cong f g p (` x)   = p x
subst-cong f g p (Π A)   =
  cong Π (subst-cong (exts f) (exts g) (exts-cong f g p) A)
subst-cong f g p (A ⇒ B) = cong₂ _⇒_ (subst-cong f g p A) (subst-cong f g p B)
subst-cong f g p (ƛ A)   =
  cong ƛ (subst-cong (exts f) (exts g) (exts-cong f g p) A)
subst-cong f g p (A · B) = cong₂ _·_ (subst-cong f g p A) (subst-cong f g p B)
subst-cong f g p (μ A)   =
  cong μ (subst-cong (exts f) (exts g) (exts-cong f g p) A)
\end{code}

First monad law for subst
\begin{code}
subst-id : ∀ {Φ J}(t : Φ ⊢⋆ J)
  → subst ` t ≡ t
subst-id (` x)   = refl
subst-id (Π A)   =
  cong Π (trans (subst-cong (exts `) ` exts-id A) (subst-id A))
subst-id (A ⇒ B) = cong₂ _⇒_ (subst-id A) (subst-id B)
subst-id (ƛ A)    =
  cong ƛ (trans (subst-cong (exts `) ` exts-id A) (subst-id A))
subst-id (A · B) = cong₂ _·_ (subst-id A) (subst-id B)
subst-id (μ A)   =
  cong μ (trans (subst-cong (exts `) ` exts-id A) (subst-id A))
\end{code}

Fusion of exts and ext
\begin{code}
exts-ext : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------
  → exts (f ∘ g) x ≡ exts f (ext g x)
exts-ext g f Z     = refl
exts-ext g f (S x) = refl
\end{code}

Fusion for subst and rename
\begin{code}
subst-rename : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -----------------------------------------
  → subst (f ∘ g) A ≡ subst f (rename g A)
subst-rename g f (` x)   = refl
subst-rename g f (Π A)   =
  cong Π
       (trans (subst-cong (exts (f ∘ g)) (exts f ∘ ext g) (exts-ext g f) A)
              (subst-rename (ext g) (exts f) A)  )
subst-rename g f (A ⇒ B) =
  cong₂ _⇒_ (subst-rename g f A) (subst-rename g f B)
subst-rename g f (ƛ A)   =
  cong ƛ
       (trans (subst-cong (exts (f ∘ g)) (exts f ∘ ext g) (exts-ext g f) A)
              (subst-rename (ext g) (exts f) A)  )
subst-rename g f (A · B) =
  cong₂ _·_ (subst-rename g f A) (subst-rename g f B)
subst-rename g f (μ A)   =
  cong μ
       (trans (subst-cong (exts (f ∘ g)) (exts f ∘ ext g) (exts-ext g f) A)
              (subst-rename (ext g) (exts f) A)  )
\end{code}

Fusion for exts and ext
\begin{code}
rename-ext-exts : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J) →
  ∀{J K}(x : Φ ,⋆ K ∋⋆ J) →
  exts (rename f ∘ g) x ≡ rename (ext f) (exts g x)
rename-ext-exts g f Z = refl
rename-ext-exts g f (S x) =
  trans (sym (rename-comp f S (g x)))
        (rename-comp S (ext f) (g x))
\end{code}

Fusion for rename and subst
\begin{code}
rename-subst : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------------
  → subst (rename f ∘ g) A ≡ rename f (subst g A)
rename-subst g f (` x)   = refl
rename-subst g f (Π A)   =
  cong Π
       (trans (subst-cong (exts (rename f ∘ g))
                          (rename (ext f) ∘ exts g)
                          (rename-ext-exts g f)
                 A)
              (rename-subst (exts g) (ext f) A))
rename-subst g f (A ⇒ B) =
  cong₂ _⇒_ (rename-subst g f A) (rename-subst g f B)
rename-subst g f (ƛ A)    =
  cong ƛ
       (trans (subst-cong (exts (rename f ∘ g))
                          (rename (ext f) ∘ exts g)
                          (rename-ext-exts g f)
                 A)
              (rename-subst (exts g) (ext f) A))
rename-subst g f (A · B) =
  cong₂ _·_ (rename-subst g f A) (rename-subst g f B)
rename-subst g f (μ A)   =
  cong μ
       (trans (subst-cong (exts (rename f ∘ g))
                          (rename (ext f) ∘ exts g)
                          (rename-ext-exts g f)
                 A)
              (rename-subst (exts g) (ext f) A))
\end{code}

Fusion of two exts
\begin{code}
extscomp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -----------------------------------------------------
  → exts (subst f ∘ g) x ≡ subst (exts f) (exts g x)
extscomp g f Z = refl
extscomp g f (S x) =
  trans (sym (rename-subst f S (g x)))
        (subst-rename S (exts f) (g x))
\end{code}

Fusion of substitutions
\begin{code}
subst-comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -----------------------------------------------
  → subst (subst f ∘ g) A ≡ subst f (subst g A)
subst-comp g f (` x)   = refl
subst-comp g f (Π A)   =
  cong Π (trans (subst-cong (exts (subst f ∘ g))
                             (subst (exts f) ∘ exts g)
                             (extscomp g f)
                             A)
                 (subst-comp (exts g) (exts f) A))
subst-comp g f (A ⇒ B) = cong₂ _⇒_ (subst-comp g f A) (subst-comp g f B)
subst-comp g f (ƛ A)    =
  cong ƛ (trans (subst-cong (exts (subst f ∘ g))
                             (subst (exts f) ∘ exts g)
                             (extscomp g f)
                             A)
                 (subst-comp (exts g) (exts f) A))
subst-comp g f (A · B) = cong₂ _·_ (subst-comp g f A) (subst-comp g f B)
subst-comp g f (μ A)   =
  cong μ (trans (subst-cong (exts (subst f ∘ g))
                             (subst (exts f) ∘ exts g)
                             (extscomp g f)
                             A)
                 (subst-comp (exts g) (exts f) A))
\end{code}

Commuting substcons and rename
\begin{code}
rename-subst-cons : ∀{Γ Δ}{J K} 
  (ρ⋆ : ∀{K} → Γ ∋⋆ K → Δ ∋⋆ K )
  → (A : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    -------------------------------------------------------------------------
  → subst-cons ` (rename ρ⋆ A) (ext ρ⋆ x) ≡ rename ρ⋆ (subst-cons ` A x)
rename-subst-cons ρ⋆ A Z     = refl
rename-subst-cons ρ⋆ A (S x) = refl
\end{code}

Commuting substcons and subst
\begin{code}
subst-subst-cons : ∀{Γ Δ}{J K} 
  (σ⋆ : ∀{K} → Γ ∋⋆ K → Δ ⊢⋆ K )
  → (M : Γ ⊢⋆ K)
  → (x : Γ ,⋆ K ∋⋆ J)
    -------------------------------------------------
  → subst (subst-cons ` (subst σ⋆ M)) (exts σ⋆ x)
    ≡
    subst σ⋆ (subst-cons ` M x)
subst-subst-cons σ⋆ M Z     = refl
subst-subst-cons σ⋆ M (S x) =
  trans (sym (subst-rename S (subst-cons ` (subst σ⋆ M)) (σ⋆ x)))
        (subst-id (σ⋆ x))
\end{code}

\begin{code}
postulate
 rename[] : ∀{Γ Δ K J}
  (ρ : ∀{K} → Γ ∋⋆ K → Δ ∋⋆ K)
  → (A : Γ ⊢⋆ K)
  → (B : Γ ,⋆ K ⊢⋆ J)
  → rename ρ (B [ A ]) ≡ rename (ext ρ) B [ rename ρ A ] 
\end{code}
