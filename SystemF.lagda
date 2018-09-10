\begin{code}
module SystemF where
\end{code}

## Imports

\begin{code}
open import Data.Product using (Σ)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋⋆_
infix  4 _∋_
infix  4 _⊢⋆_
infix  4 _⊢_
infixl 5 _,⋆_
infixl 5 _,_

infix  6 Π_
infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 S_
\end{code}

## Kinds

The only kind is `*`, the kind of types.
\begin{code}
data Kind : Set where
  * : Kind
  _⇒_ : Kind → Kind → Kind
\end{code}
Let `J`, `K` range over kinds.

## Type contexts

A type context is either empty or extends a type
context by a type variable of a given kind.
\begin{code}
data Ctx⋆ : Set where
  ∅ : Ctx⋆
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆
\end{code}
Let `Φ`, `Ψ` range over type contexts.

## Type variables

A type variable is indexed by its context and kind.
\begin{code}
data _∋⋆_ : Ctx⋆ → Kind → Set where

  Z : ∀ {Φ J}
      -------------
    → Φ ,⋆ J ∋⋆ J

  S_ : ∀ {Φ J K} -- S_ permits things like 'S f x' as well as 'S (f x)'...
    → Φ ∋⋆ J
      -------------
    → Φ ,⋆ K ∋⋆ J
\end{code}
Let `α`, `β` range over type variables.

## Types

A type is indexed by its context and kind.  A type is either a type
variable, a pi type, or a function type.
\begin{code}
data _⊢⋆_ : Ctx⋆ → Kind → Set where

  `_ : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢⋆ J

  Π_ : ∀ {Φ K}
    → Φ ,⋆ K ⊢⋆ *
      -----------
    → Φ ⊢⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢⋆ *
    → Φ ⊢⋆ *
      ------
    → Φ ⊢⋆ *

  ƛ_ :  ∀ {Φ K J}
    → Φ ,⋆ K ⊢⋆ J 
      -----------
    → Φ ⊢⋆ K ⇒ J

  _·_ : ∀{Φ K J}
    → Φ ⊢⋆ K ⇒ J
    → Φ ⊢⋆ K
      ------
    → Φ ⊢⋆ J

  μ_ : ∀{φ K}
    → φ ,⋆ K ⊢⋆ *
      -----------
    → φ ⊢⋆ *

\end{code}
Let `A`, `B`, `C` range over types.

## Type renaming

A type renaming is a mapping of type variables to type variables.

Extending a type renaming — used when going under a binder.
\begin{code}
ext⋆ : ∀ {Φ Ψ} → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ------------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ∋⋆ J)
ext⋆ ρ Z      =  Z
ext⋆ ρ (S α)  =  S (ρ α)
\end{code}

Apply a type renaming to a type.
\begin{code}
rename⋆ : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
rename⋆ ρ (` α)    =  ` (ρ α)
rename⋆ ρ (Π B)    =  Π (rename⋆ (ext⋆ ρ) B)
rename⋆ ρ (A ⇒ B)  =  rename⋆ ρ A ⇒ rename⋆ ρ B
rename⋆ ρ (ƛ B)    = ƛ rename⋆ (ext⋆ ρ) B
rename⋆ ρ (A · B)  = rename⋆ ρ A · rename⋆ ρ B
rename⋆ ρ (μ B)    =  μ (rename⋆ (ext⋆ ρ) B)
\end{code}

Weakening is a special case of renaming.
\begin{code}
weaken⋆ : ∀ {Φ J K}
  → Φ ⊢⋆ J
    -------------
  → Φ ,⋆ K ⊢⋆ J
weaken⋆ = rename⋆ S_
\end{code}

## Renaming proofs

First functor law for ext⋆
\begin{code}
ext⋆id :  ∀ {Φ J K} → (x : Φ ,⋆ K ∋⋆ J) → ext⋆ id x ≡ x
ext⋆id Z     = refl
ext⋆id (S x) = refl
\end{code}

This congruence lemma and analogous ones for exts⋆, rename⋆, and
subst⋆ avoids the use of extensionality when reasoning about equal
renamings/substitutions as we only need a pointwise version of
equality. If we used the standard library's cong we would need to
postulate extensionality and our equality proofs wouldn't compute. I
learnt this from Conor McBride.
\begin{code}
ext⋆cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ J ∋⋆ K)
    -------------------
  → ext⋆ f x ≡ ext⋆ g x
ext⋆cong f g p Z     = refl
ext⋆cong f g p (S x) = cong S_ (p x)
\end{code}
Congruence lemma for renaming⋆
\begin{code}
rename⋆cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -------------------------
  → rename⋆ f A ≡ rename⋆ g A
rename⋆cong f g p (` x)   = cong `_ (p x)
rename⋆cong f g p (Π A)   =
  cong Π_ (rename⋆cong (ext⋆ f) (ext⋆ g) (ext⋆cong f g p) A)
rename⋆cong f g p (A ⇒ B) =
  cong₂ _⇒_ (rename⋆cong f g p A) (rename⋆cong f g p B)
rename⋆cong f g p (ƛ A)   =
  cong ƛ_ (rename⋆cong (ext⋆ f) (ext⋆ g) (ext⋆cong f g p) A)
rename⋆cong f g p (A · B) =
  cong₂ _·_ (rename⋆cong f g p A) (rename⋆cong f g p B)
rename⋆cong f g p (μ A)   =
  cong μ_ (rename⋆cong (ext⋆ f) (ext⋆ g) (ext⋆cong f g p) A)
\end{code}

First functor law for rename⋆
\begin{code}
rename⋆id : ∀{Φ J}(t : Φ ⊢⋆ J) → rename⋆ id t ≡ t
rename⋆id (` x)   = refl
rename⋆id (Π t)   =
  cong Π_ (trans (rename⋆cong (ext⋆ id) id ext⋆id t) (rename⋆id t))
rename⋆id (t ⇒ u) = cong₂ _⇒_ (rename⋆id t) (rename⋆id u)
rename⋆id (ƛ t)   =
  cong ƛ_ (trans (rename⋆cong (ext⋆ id) id ext⋆id t) (rename⋆id t))
rename⋆id (t · u) = cong₂ _·_ (rename⋆id t) (rename⋆id u)
rename⋆id (μ t)   =
  cong μ_ (trans (rename⋆cong (ext⋆ id) id ext⋆id t) (rename⋆id t))

\end{code}

Second functor law for ext⋆
\begin{code}
ext⋆comp : ∀{Φ Ψ Θ}(g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ----------------------------------
  → ext⋆ (f ∘ g) x ≡ ext⋆ f (ext⋆ g x)
ext⋆comp g f Z     = refl
ext⋆comp g f (S x) = refl
\end{code}

Second functor law for renaming⋆
\begin{code}
rename⋆comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------
  → rename⋆ (f ∘ g) A ≡ rename⋆ f (rename⋆ g A)
rename⋆comp g f (` x)   = refl
rename⋆comp g f (Π A)   =
  cong Π_
       (trans (rename⋆cong (ext⋆ (f ∘ g)) (ext⋆ f ∘ ext⋆ g) (ext⋆comp g f) A)
              (rename⋆comp (ext⋆ g) (ext⋆ f) A))
rename⋆comp g f (A ⇒ B) = cong₂ _⇒_ (rename⋆comp g f A) (rename⋆comp g f B)
rename⋆comp g f (ƛ A) = 
  cong ƛ_
       (trans (rename⋆cong (ext⋆ (f ∘ g)) (ext⋆ f ∘ ext⋆ g) (ext⋆comp g f) A)
              (rename⋆comp (ext⋆ g) (ext⋆ f) A))
rename⋆comp g f (A · B) = cong₂ _·_ (rename⋆comp g f A) (rename⋆comp g f B)
rename⋆comp g f (μ A)   =
  cong μ_
       (trans (rename⋆cong (ext⋆ (f ∘ g)) (ext⋆ f ∘ ext⋆ g) (ext⋆comp g f) A)
              (rename⋆comp (ext⋆ g) (ext⋆ f) A))
\end{code}
## Type substitution

A type substitution is a mapping of type variables to types.

Extending a type substitution — used when going under a binder.
\begin{code}
exts⋆ : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢⋆ J)
exts⋆ σ Z      =  ` Z
exts⋆ σ (S α)  =  weaken⋆ (σ α)
\end{code}

Apply a type substitution to a type.
\begin{code}
subst⋆ : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
subst⋆ σ (` α)     =  σ α
subst⋆ σ (Π B)     =  Π (subst⋆ (exts⋆ σ) B)
subst⋆ σ (A ⇒ B)   =  subst⋆ σ A ⇒ subst⋆ σ B
subst⋆ σ (ƛ B)     =  ƛ (subst⋆ (exts⋆ σ) B)
subst⋆ σ (A · B)   =  subst⋆ σ A · subst⋆ σ B
subst⋆ σ (μ B)     =  μ (subst⋆ (exts⋆ σ) B)
\end{code}

Extend a substitution with an additional type (analogous to cons for
backward lists)
\begin{code}
subst⋆cons : ∀{Φ Ψ} → (∀{K} → Φ ∋⋆ K → Ψ ⊢⋆ K) → ∀{J}(A : Ψ ⊢⋆ J) →
             (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢⋆ K)
subst⋆cons f A Z = A
subst⋆cons f A (S x) = f x
\end{code}

A special case is substitution a type for the outermost free variable.
\begin{code}
_[_]⋆ : ∀ {Φ J K}
        → Φ ,⋆ K ⊢⋆ J
        → Φ ⊢⋆ K 
          ------
        → Φ ⊢⋆ J
_[_]⋆ {Φ} {J} {K} B A =  subst⋆ (subst⋆cons `_ A) B
\end{code}

## Type Substitution Proofs

Extending the identity substitution yields the identity substitution
\begin{code}
exts⋆id : ∀ {Φ J K}(x : Φ ,⋆ K ∋⋆ J)
    ----------------
  → exts⋆ `_ x ≡ ` x 
exts⋆id Z     = refl
exts⋆id (S x) = refl
\end{code}

Congruence lemma for exts⋆
\begin{code}
exts⋆cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -----------------------
  → exts⋆ f x ≡ exts⋆ g x
exts⋆cong f g p Z     = refl
exts⋆cong f g p (S x) = cong weaken⋆ (p x)
\end{code}

Congruence lemma for subst⋆
\begin{code}
subst⋆cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢⋆ K)
    -----------------------
  → subst⋆ f A ≡ subst⋆ g A
subst⋆cong f g p (` x)   = p x
subst⋆cong f g p (Π A)   =
  cong Π_ (subst⋆cong (exts⋆ f) (exts⋆ g) (exts⋆cong f g p) A)
subst⋆cong f g p (A ⇒ B) = cong₂ _⇒_ (subst⋆cong f g p A) (subst⋆cong f g p B)
subst⋆cong f g p (ƛ A)   =
  cong ƛ_ (subst⋆cong (exts⋆ f) (exts⋆ g) (exts⋆cong f g p) A)
subst⋆cong f g p (A · B) = cong₂ _·_ (subst⋆cong f g p A) (subst⋆cong f g p B)
subst⋆cong f g p (μ A)   =
  cong μ_ (subst⋆cong (exts⋆ f) (exts⋆ g) (exts⋆cong f g p) A)
\end{code}

First monad law for subst⋆
\begin{code}
subst⋆id : ∀ {Φ J}(t : Φ ⊢⋆ J)
  → subst⋆ `_ t ≡ t
subst⋆id (` x)   = refl
subst⋆id (Π A)   =
  cong Π_ (trans (subst⋆cong (exts⋆ `_) `_ exts⋆id A) (subst⋆id A))
subst⋆id (A ⇒ B) = cong₂ _⇒_ (subst⋆id A) (subst⋆id B)
subst⋆id (ƛ A)    =
  cong ƛ_ (trans (subst⋆cong (exts⋆ `_) `_ exts⋆id A) (subst⋆id A))
subst⋆id (A · B) = cong₂ _·_ (subst⋆id A) (subst⋆id B)
subst⋆id (μ A)   =
  cong μ_ (trans (subst⋆cong (exts⋆ `_) `_ exts⋆id A) (subst⋆id A))
\end{code}

Fusion of exts⋆ and ext⋆
\begin{code}
exts⋆ext⋆ : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    ------------------------------------
  → exts⋆ (f ∘ g) x ≡ exts⋆ f (ext⋆ g x)
exts⋆ext⋆ g f Z     = refl
exts⋆ext⋆ g f (S x) = refl
\end{code}

Fusion for subst⋆ and rename⋆
\begin{code}
subst⋆rename⋆ : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -----------------------------------------
  → subst⋆ (f ∘ g) A ≡ subst⋆ f (rename⋆ g A)
subst⋆rename⋆ g f (` x)   = refl
subst⋆rename⋆ g f (Π A)   =
  cong Π_
       (trans (subst⋆cong (exts⋆ (f ∘ g)) (exts⋆ f ∘ ext⋆ g) (exts⋆ext⋆ g f) A)
              (subst⋆rename⋆ (ext⋆ g) (exts⋆ f) A)  )
subst⋆rename⋆ g f (A ⇒ B) =
  cong₂ _⇒_ (subst⋆rename⋆ g f A) (subst⋆rename⋆ g f B)
subst⋆rename⋆ g f (ƛ A)   =
  cong ƛ_
       (trans (subst⋆cong (exts⋆ (f ∘ g)) (exts⋆ f ∘ ext⋆ g) (exts⋆ext⋆ g f) A)
              (subst⋆rename⋆ (ext⋆ g) (exts⋆ f) A)  )
subst⋆rename⋆ g f (A · B) =
  cong₂ _·_ (subst⋆rename⋆ g f A) (subst⋆rename⋆ g f B)
subst⋆rename⋆ g f (μ A)   =
  cong μ_
       (trans (subst⋆cong (exts⋆ (f ∘ g)) (exts⋆ f ∘ ext⋆ g) (exts⋆ext⋆ g f) A)
              (subst⋆rename⋆ (ext⋆ g) (exts⋆ f) A)  )
\end{code}

Fusion for exts⋆ and ext⋆
\begin{code}
rename⋆ext⋆exts⋆ : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J) →
  ∀{J K}(x : Φ ,⋆ K ∋⋆ J) →
  exts⋆ (rename⋆ f ∘ g) x ≡ rename⋆ (ext⋆ f) (exts⋆ g x)
rename⋆ext⋆exts⋆ g f Z = refl
rename⋆ext⋆exts⋆ g f (S x) =
  trans (sym (rename⋆comp f S_ (g x)))
        (rename⋆comp S_ (ext⋆ f) (g x))
\end{code}

Fusion for rename⋆ and subst⋆
\begin{code}
rename⋆subst⋆ : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -------------------------------------------------
  → subst⋆ (rename⋆ f ∘ g) A ≡ rename⋆ f (subst⋆ g A)
rename⋆subst⋆ g f (` x)   = refl
rename⋆subst⋆ g f (Π A)   =
  cong Π_
       (trans (subst⋆cong (exts⋆ (rename⋆ f ∘ g))
                          (rename⋆ (ext⋆ f) ∘ exts⋆ g)
                          (rename⋆ext⋆exts⋆ g f)
                 A)
              (rename⋆subst⋆ (exts⋆ g) (ext⋆ f) A))
rename⋆subst⋆ g f (A ⇒ B) =
  cong₂ _⇒_ (rename⋆subst⋆ g f A) (rename⋆subst⋆ g f B)
rename⋆subst⋆ g f (ƛ A)    =
  cong ƛ_
       (trans (subst⋆cong (exts⋆ (rename⋆ f ∘ g))
                          (rename⋆ (ext⋆ f) ∘ exts⋆ g)
                          (rename⋆ext⋆exts⋆ g f)
                 A)
              (rename⋆subst⋆ (exts⋆ g) (ext⋆ f) A))
rename⋆subst⋆ g f (A · B) =
  cong₂ _·_ (rename⋆subst⋆ g f A) (rename⋆subst⋆ g f B)
rename⋆subst⋆ g f (μ A)   =
  cong μ_
       (trans (subst⋆cong (exts⋆ (rename⋆ f ∘ g))
                          (rename⋆ (ext⋆ f) ∘ exts⋆ g)
                          (rename⋆ext⋆exts⋆ g f)
                 A)
              (rename⋆subst⋆ (exts⋆ g) (ext⋆ f) A))
\end{code}

Fusion of two exts⋆
\begin{code}
exts⋆comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
    -----------------------------------------------------
  → exts⋆ (subst⋆ f ∘ g) x ≡ subst⋆ (exts⋆ f) (exts⋆ g x)
exts⋆comp g f Z = refl
exts⋆comp g f (S x) =
  trans (sym (rename⋆subst⋆ f S_ (g x)))
        (subst⋆rename⋆ S_ (exts⋆ f) (g x))
\end{code}

Fusion of substitutions
\begin{code}
subst⋆comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢⋆ J)
  → ∀{J}(A : Φ ⊢⋆ J)
    -----------------------------------------------
  → subst⋆ (subst⋆ f ∘ g) A ≡ subst⋆ f (subst⋆ g A)
subst⋆comp g f (` x)   = refl
subst⋆comp g f (Π A)   =
  cong Π_ (trans (subst⋆cong (exts⋆ (subst⋆ f ∘ g))
                             (subst⋆ (exts⋆ f) ∘ exts⋆ g)
                             (exts⋆comp g f)
                             A)
                 (subst⋆comp (exts⋆ g) (exts⋆ f) A))
subst⋆comp g f (A ⇒ B) = cong₂ _⇒_ (subst⋆comp g f A) (subst⋆comp g f B)
subst⋆comp g f (ƛ A)    =
  cong ƛ_ (trans (subst⋆cong (exts⋆ (subst⋆ f ∘ g))
                             (subst⋆ (exts⋆ f) ∘ exts⋆ g)
                             (exts⋆comp g f)
                             A)
                 (subst⋆comp (exts⋆ g) (exts⋆ f) A))
subst⋆comp g f (A · B) = cong₂ _·_ (subst⋆comp g f A) (subst⋆comp g f B)
subst⋆comp g f (μ A)   =
  cong μ_ (trans (subst⋆cong (exts⋆ (subst⋆ f ∘ g))
                             (subst⋆ (exts⋆ f) ∘ exts⋆ g)
                             (exts⋆comp g f)
                             A)
                 (subst⋆comp (exts⋆ g) (exts⋆ f) A))
\end{code}

Commuting subst⋆cons and rename⋆
\begin{code}
rename⋆subst⋆cons : ∀{Γ Δ}{J} 
  (ρ⋆ : ∀{K} → Γ ∋⋆ K → Δ ∋⋆ K )
  → (A : Γ ⊢⋆ *)
  → (x : Γ ,⋆ * ∋⋆ J)
    -------------------------------------------------------------------------
  → subst⋆cons `_ (rename⋆ ρ⋆ A) (ext⋆ ρ⋆ x) ≡ rename⋆ ρ⋆ (subst⋆cons `_ A x)
rename⋆subst⋆cons ρ⋆ A Z     = refl
rename⋆subst⋆cons ρ⋆ A (S x) = refl
\end{code}

Commuting subst⋆cons and subst⋆
\begin{code}
subst⋆subst⋆cons : ∀{Γ Δ}{J} 
  (σ⋆ : ∀{K} → Γ ∋⋆ K → Δ ⊢⋆ K )
  → (M : Γ ⊢⋆ *)
  → (x : Γ ,⋆ * ∋⋆ J)
    -------------------------------------------------
  → subst⋆ (subst⋆cons `_ (subst⋆ σ⋆ M)) (exts⋆ σ⋆ x)
    ≡
    subst⋆ σ⋆ (subst⋆cons `_ M x)
subst⋆subst⋆cons σ⋆ M Z     = refl
subst⋆subst⋆cons σ⋆ M (S x) =
  trans (sym (subst⋆rename⋆ S_ (subst⋆cons `_ (subst⋆ σ⋆ M)) (σ⋆ x)))
        (subst⋆id (σ⋆ x))
\end{code}


## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
data Ctx : Set
∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx where
  ∅ : Ctx
  _,⋆_ : Ctx → Kind → Ctx
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Ctx
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
∥ ∅ ∥       =  ∅
∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken⋆ A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  `_ : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Γ B}
    → Γ ⊢ Π B
    → (A : ∥ Γ ∥ ⊢⋆ *)
      ---------------
    → Γ ⊢ B [ A ]⋆

  wrap : ∀{Γ}
    → (S : ∥ Γ ∥ ,⋆ * ⊢⋆ *)
    → (M : Γ ⊢ S [ μ S ]⋆)
    → Γ ⊢ μ S

  unwrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → (M : Γ ⊢ μ S)
    → Γ ⊢ S [ μ S ]⋆
\end{code}

## Remainder

The development continues from here as in
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}),
defining renaming and substitution on terms and introducing reduction
rules for terms, proving progress, and applying progress to derive an
evaluator.

## Renaming

\begin{code}
ext : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ rename⋆ ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K } {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
     → Γ , B ∋ A
       -------------------------------
     → Δ , rename⋆ ρ⋆ B ∋ rename⋆ ρ⋆ A)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
ext⋆⋆ : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ rename⋆ ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ∋ rename⋆ (ext⋆ ρ⋆) A )
ext⋆⋆ {Γ}{Δ} ρ⋆ ρ {J}{K}{A} (T x) =
  substEq (λ A → Δ ,⋆ K ∋ A)
          (trans (sym (rename⋆comp ρ⋆ S_ _)) (rename⋆comp S_ (ext⋆ ρ⋆) _))
          (T (ρ x))
\end{code}

\begin{code}
rename : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {J} → ∥ Γ ∥ ∋⋆ J → ∥ Δ ∥ ∋⋆ J)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ∋ rename⋆ ρ⋆ A)
    ------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Δ ⊢ rename⋆ ρ⋆ A )
rename ρ⋆ ρ (` x)    = ` (ρ x)
rename ρ⋆ ρ (ƛ N)    = ƛ (rename ρ⋆ (ext ρ⋆ ρ) N)
rename ρ⋆ ρ (L · M)  = rename ρ⋆ ρ L · rename ρ⋆ ρ M 
rename ρ⋆ ρ (Λ N)    = Λ rename (ext⋆ ρ⋆) (ext⋆⋆ ρ⋆ ρ) N 
rename {Γ}{Δ} ρ⋆ ρ (_·⋆_ {B = B} t A) =
  substEq (λ A → Δ ⊢ A)
          ( trans (sym (subst⋆rename⋆ (ext⋆ ρ⋆)
                                      (subst⋆cons `_ (rename⋆ ρ⋆ A))
                                      B))
                 (trans (subst⋆cong _ _ (rename⋆subst⋆cons ρ⋆ A) B)
                        (rename⋆subst⋆ (subst⋆cons `_ A) ρ⋆ B) ) )
          (rename ρ⋆ ρ t ·⋆ rename⋆ ρ⋆ A)
rename {Γ}{Δ} ρ⋆ ρ (wrap M N) =
  wrap (rename⋆ (ext⋆ ρ⋆) M)
       (substEq (λ A → Δ ⊢ A)
                (trans (sym (rename⋆subst⋆ (subst⋆cons `_ (μ M)) ρ⋆ M))
                       (trans (subst⋆cong
                                 _
                                 _
                                 (λ x → sym (rename⋆subst⋆cons _ _ x)) M)
                              (subst⋆rename⋆
                                (ext⋆ ρ⋆)
                                (subst⋆cons `_ (μ (rename⋆ (ext⋆ ρ⋆) M))) M)))
                (rename ρ⋆ ρ N))
rename {Γ}{Δ} ρ⋆ ρ (unwrap {S = S} M) =
  substEq (λ A → Δ ⊢ A)
          (trans (sym (subst⋆rename⋆ _ _ S))
                 (trans (subst⋆cong _ _ (rename⋆subst⋆cons _ _) S)
                        (rename⋆subst⋆ _ _ S)))
          (unwrap (rename ρ⋆ ρ M))
\end{code}

\begin{code}
weaken : ∀ {Φ J}{A : ∥ Φ ∥ ⊢⋆ J}{K}{B : ∥ Φ ∥ ⊢⋆ K}
  → Φ ⊢ A
    -------------
  → Φ , B ⊢ A
weaken {Φ}{J}{A}{K}{B} x =
  substEq (λ x → Φ , B ⊢ x)
          (rename⋆id A)
          (rename id
                  (λ x → substEq (λ A → Φ , B ∋ A) (sym (rename⋆id _)) (S x))
                  x)
\end{code}

\begin{code}
weaken⋆⋆ : ∀ {Φ J}{A : ∥ Φ ∥ ⊢⋆ J}{K}
  → Φ ⊢ A
    ------------------
  → Φ ,⋆ K ⊢ weaken⋆ A
weaken⋆⋆ x = rename _∋⋆_.S_ _∋_.T_ x
\end{code}

## Substitution
\begin{code}
exts : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ subst⋆ σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
     → Γ , B ∋ A
     -------------------------------
     → Δ , subst⋆ σ⋆ B ⊢ subst⋆ σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆⋆ : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ subst⋆ σ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ subst⋆ (exts⋆ σ⋆) A )
exts⋆⋆ {Γ}{Δ} σ⋆ σ {J}{K}(T_ {A = A} x) =
  substEq (λ x → Δ ,⋆ K ⊢ x)
          (trans (sym (rename⋆subst⋆ σ⋆ S_ A)) (subst⋆rename⋆ S_ (exts⋆ σ⋆) A))
          (weaken⋆⋆ (σ x))

\end{code}

\begin{code}
subst : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ subst⋆ σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Δ ⊢ subst⋆ σ⋆ A)
subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ N)                     = ƛ (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst σ⋆ σ (Λ N)                     = Λ subst (exts⋆ σ⋆) (exts⋆⋆ σ⋆ σ) N
subst {Γ}{Δ} σ⋆ σ (_·⋆_ {B = B} L M) =
  substEq (λ A → Δ ⊢ A)
          (trans (sym (subst⋆comp (exts⋆ σ⋆) (subst⋆cons `_ (subst⋆ σ⋆ M)) B))
                 (trans (subst⋆cong (subst⋆ (subst⋆cons `_ (subst⋆ σ⋆ M))
                                     ∘
                                     exts⋆ σ⋆)
                                    (subst⋆ σ⋆ ∘ subst⋆cons `_ M)
                                    (subst⋆subst⋆cons σ⋆ M)
                                    B)
                        (subst⋆comp (subst⋆cons `_ M) σ⋆ B)))
          (subst σ⋆ σ L ·⋆ subst⋆ σ⋆ M)
subst {Γ}{Δ} σ⋆ σ (wrap M N) =
  wrap (subst⋆ (exts⋆ σ⋆) M)
       (substEq (λ A → Δ ⊢ A)
                (trans (sym (subst⋆comp (subst⋆cons `_ (μ M)) σ⋆ M))
                       (trans (subst⋆cong
                                _
                                _
                                (λ x → sym (subst⋆subst⋆cons _ _ x))
                                M)
                              (subst⋆comp
                                (exts⋆ σ⋆)
                                (subst⋆cons `_ (μ (subst⋆ (exts⋆ σ⋆) M)))
                                M)))
                (subst σ⋆ σ N))
subst {Γ}{Δ} σ⋆ σ (unwrap {S = S} M) =
  substEq (λ A → Δ ⊢ A)
          (trans (trans (sym (subst⋆comp _ _ S))
                        (subst⋆cong _ _ (subst⋆subst⋆cons _ _) S))
                 (subst⋆comp _ _ S))
          (unwrap (subst σ⋆ σ M))
\end{code}

\begin{code}
substcons : ∀{Γ Δ} →
  (σ⋆ : ∀{K} → ∥ Γ ∥  ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J}{A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ subst⋆ σ⋆ A)
  → ∀{J}{A : ∥ Γ ∥ ⊢⋆ J}
  → (t : Δ ⊢ subst⋆ σ⋆ A)
    ---------------------
  → (∀ {J} {B : ∥ Γ ∥ ⊢⋆ J} → Γ , A ∋ B → Δ ⊢ subst⋆ σ⋆ B)
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
          (subst⋆id A)
          (subst `_
                 (substcons `_
                            (λ x → substEq (λ A → Γ ⊢ A)
                                           (sym (subst⋆id _))
                                           (` x))
                            (substEq (λ A → Γ ⊢ A) (sym (subst⋆id B)) s))
                 t) 
\end{code}

\begin{code}
_[_]⋆⋆ : ∀ {J Γ K} {B : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
        → Γ ,⋆ K ⊢ B
        → (A : ∥ Γ ∥ ⊢⋆ K)
          ---------
        → Γ ⊢ B [ A ]⋆
_[_]⋆⋆ {J}{Γ}{K}{B} t A =
  subst (subst⋆cons `_ A)
        (λ{(T_ {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (sym (subst⋆id A'))
                                     (subst⋆rename⋆ S_ (subst⋆cons `_ A) A'))
                                     (` x)})
          t
\end{code}
0
## Values

\begin{code}
data Value⋆ :  ∀ {Γ K} → Γ ⊢⋆ K → Set where

  V-Π_ : ∀ {Φ K} {N : Φ ,⋆ K ⊢⋆ *}
      ----------------------------
    → Value⋆ (Π N)

  _V-⇒_ : ∀ {Φ} {S : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
      -----------------------------------
    → Value⋆ (S ⇒ T)

  V-ƛ_ : ∀ {Φ K J} {N : Φ ,⋆ K ⊢⋆ J}
      ----------------------------
    → Value⋆ (ƛ N)

  V-μ_ : ∀ {Φ K} {N : Φ ,⋆ K ⊢⋆ *}
      ----------------------------
    → Value⋆ (μ N)

data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M : Γ ⊢ S [ μ S ]⋆}
      ----------------
    → Value (wrap S M)
\end{code}

## Intrinsically Kind Preserving Type Reduction

\begin{code}
infix 2 _—→⋆_

data _—→⋆_ : ∀ {Γ J} → (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where
  ξ-·₁ : ∀ {Γ K J} {L L′ : Γ ⊢⋆ K ⇒ J} {M : Γ ⊢⋆ K}
    → L —→⋆ L′
      -----------------
    → L · M —→⋆ L′ · M

  ξ-·₂ : ∀ {Γ K J} {V : Γ ⊢⋆ K ⇒ J} {M M′ : Γ ⊢⋆ K}
    → Value⋆ V
    → M —→⋆ M′
      --------------
    → V · M —→⋆ V · M′


  β-ƛ : ∀ {Γ K J} {N : Γ ,⋆ K ⊢⋆ J} {W : Γ ⊢⋆ K}
    → Value⋆ W
      -------------------
    → (ƛ N) · W —→⋆ N [ W ]⋆
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Γ B}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A
    
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ}{B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}{N : Γ ,⋆ * ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆⋆

  ξ-unwrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M M' : Γ ⊢ μ S}
    → M —→ M'
    → unwrap M —→ unwrap M'

  β-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M : Γ ⊢ S [ μ S ]⋆}    
    → unwrap (wrap S M) —→ M
\end{code}

\begin{code}
data Progress⋆ {K} (M : ∅ ⊢⋆ K) : Set where
  step : ∀ {N : ∅ ⊢⋆ K}
    → M —→⋆ N
      -------------
    → Progress⋆ M
  done :
      Value⋆ M
      ----------
    → Progress⋆ M
\end{code}

\begin{code}
progress⋆ : ∀ {K} → (M : ∅ ⊢⋆ K) → Progress⋆ M
progress⋆ (` ())
progress⋆ (Π M)   = done V-Π_
progress⋆ (M ⇒ N) = done _V-⇒_
progress⋆ (ƛ M)   = done V-ƛ_
progress⋆ (M · N)  with progress⋆ M
...                    | step p = step (ξ-·₁ p)
...                    | done vM with progress⋆ N
...                                | step p = step (ξ-·₂ vM p)
progress⋆ (.(ƛ _) · N) | done V-ƛ_ | done vN = step (β-ƛ vN)
progress⋆ (μ M)   = done V-μ_
\end{code}

\begin{code}
data Progress {A : ∅ ⊢⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀ {N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | step p  = step (ξ-·₁ p)
...                   | done vL with progress M
...                              | step p  = step (ξ-·₂ vL p)
progress (.(ƛ _) · M) | done V-ƛ | done vM = step (β-ƛ vM)
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A)      | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap A M) = done V-wrap
progress (unwrap M) with progress M
progress (unwrap M) | step p = step (ξ-unwrap p)
progress (unwrap .(wrap _ _)) | done V-wrap = step β-wrap
\end{code}

## Evaluation

Transitive closure of reduction
\begin{code}
data _—↠_ {J Γ}{A : ∥ Γ ∥ ⊢⋆ J} (L : Γ ⊢ A) : (Γ ⊢ A) → Set where
  done : L —↠ L
  continue : ∀ {M N} → L —→ M → M —↠ N → L —↠ N  
\end{code}

As previously, gas is specified by a natural number.
\begin{code}
open import Data.Nat
data Gas : Set where
  gas : ℕ → Gas
\end{code}
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas.
\begin{code}
data Finished {Γ J}{A : ∥ Γ ∥ ⊢⋆ J} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
\end{code}
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished.
\begin{code}
data Steps : ∀ {J}{A : ∅ ⊢⋆ J} → ∅ ⊢ A → Set where

  steps : ∀ {J}{A : ∅ ⊢⋆ J} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
\end{code}
The evaluator takes gas and a term and returns the corresponding steps.
\begin{code}
eval : ∀ {A : ∅ ⊢⋆ *}
  → Gas
  → (M : ∅ ⊢ A)
    -----------
  → Steps M
eval (gas zero) M = steps done out-of-gas
eval (gas (suc n)) M with progress M
eval (gas (suc n)) M | step {N} p  with eval (gas n) N
eval (gas (suc n)) M | step {N} p | steps ps q = steps (continue p ps) q
eval (gas (suc n)) M | done vM = steps done (done vM)
\end{code}
