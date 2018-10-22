\begin{code}
module Type.BetaNormal where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _⊢Nf⋆_
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Data.Product
open import Data.Unit
open import Function
\end{code}

## Type β-normal forms

\begin{code}

data _⊢Nf⋆_ : Ctx⋆ → Kind → Set

data _⊢NeN⋆_ : Ctx⋆ → Kind → Set where
  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢NeN⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢NeN⋆ (K ⇒ J)
    → Φ ⊢Nf⋆ K
      ------
    → Φ ⊢NeN⋆ J

  μ : ∀{φ K}
    → φ ,⋆ K ⊢Nf⋆ K
      -----------
    → φ ⊢NeN⋆ K



data _⊢Nf⋆_ where

  Π : ∀ {Φ K}
    → Φ ,⋆ K ⊢Nf⋆ *
      -----------
    → Φ ⊢Nf⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢Nf⋆ *
    → Φ ⊢Nf⋆ *
      ------
    → Φ ⊢Nf⋆ *

  ƛ :  ∀ {Φ K J}
    → Φ ,⋆ K ⊢Nf⋆ J
      -----------
    → Φ ⊢Nf⋆ (K ⇒ J)

  ne : ∀{φ K}
    → φ ⊢NeN⋆ K
      --------
    → φ ⊢Nf⋆ K
\end{code}

\begin{code}
renameNf : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
renameNeN : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢NeN⋆ J → Ψ ⊢NeN⋆ J)

renameNf ρ (Π A)   = Π (renameNf (ext ρ) A)
renameNf ρ (A ⇒ B) = renameNf ρ A ⇒ renameNf ρ B
renameNf ρ (ƛ B)   = ƛ (renameNf (ext ρ) B)

renameNf ρ (ne A)  = ne (renameNeN ρ A)

renameNeN ρ (` x) = ` (ρ x)
renameNeN ρ (A · x) = renameNeN ρ A · renameNf ρ x
renameNeN ρ (μ B)   = μ (renameNf (ext ρ) B)
\end{code}

\begin{code}
weakenNf : ∀ {Φ J K}
  → Φ ⊢Nf⋆ J
    -------------
  → Φ ,⋆ K ⊢Nf⋆ J
weakenNf = renameNf S
\end{code}

\begin{code}
renameNeN-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢NeN⋆ K)
    -------------------------
  → renameNeN f A ≡ renameNeN g A

renameNf-cong : ∀ {Φ Ψ}(f g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Nf⋆ K)
    -------------------------
  → renameNf f A ≡ renameNf g A
renameNf-cong f g p (Π A)   =
  cong Π (renameNf-cong (ext f) (ext g) (ext-cong p) A)
renameNf-cong f g p (A ⇒ B) =
  cong₂ _⇒_ (renameNf-cong f g p A) (renameNf-cong f g p B)
renameNf-cong f g p (ƛ A)   =
  cong ƛ (renameNf-cong (ext f) (ext g) (ext-cong p) A)
renameNf-cong f g p (ne A) = cong ne (renameNeN-cong f g p A)

renameNeN-cong f g p (` x)   = cong ` (p x)
renameNeN-cong f g p (A · B) =
  cong₂ _·_ (renameNeN-cong f g p A) (renameNf-cong f g p B)
renameNeN-cong f g p (μ A)   =
  cong μ (renameNf-cong (ext f) (ext g) (ext-cong p) A)
\end{code}

\begin{code}
mutual
  renameNf-id : ∀ {Φ}
      ----------------------------
    → ∀ {J}
    → (n : Φ ⊢Nf⋆ J)
    → renameNf id n ≡ n
  renameNf-id (Π n) = cong Π (trans (renameNf-cong _ _ ext-id n) (renameNf-id n))
  renameNf-id (n ⇒ n') = cong₂ _⇒_ (renameNf-id n) (renameNf-id n')
  renameNf-id (ƛ n) = cong ƛ (trans (renameNf-cong _ _ ext-id n) (renameNf-id n))
  renameNf-id (ne x) = cong ne (renameNeN-id x)
  
  renameNeN-id : ∀ {Φ}
      ----------------------------
    → ∀ {J}
    → (n : Φ ⊢NeN⋆ J)
    → renameNeN id n ≡ n
  renameNeN-id (` x) = refl
  renameNeN-id (n · n') = cong₂ _·_ (renameNeN-id n) (renameNf-id n')
  renameNeN-id (μ n) = cong μ (trans (renameNf-cong _ _ ext-id n) (renameNf-id n))

\end{code}

\begin{code}
mutual
  renameNf-comp : ∀{Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
    → ∀{J}(A : Φ ⊢Nf⋆ J)
      -------------------------------------------
    → renameNf (f ∘ g) A ≡ renameNf f (renameNf g A)
  renameNf-comp g f (Π B) =
    cong Π (trans (renameNf-cong _ _ ext-comp B)
                  (renameNf-comp (ext g) (ext f) B))
  renameNf-comp g f (A ⇒ B) =
    cong₂ _⇒_ (renameNf-comp g f A) (renameNf-comp g f B)
  renameNf-comp g f (ƛ B) = 
    cong ƛ (trans (renameNf-cong _ _ ext-comp B)
                  (renameNf-comp (ext g) (ext f) B))
  renameNf-comp g f (ne n) = cong ne (renameNeN-comp g f n)

  renameNeN-comp : ∀{Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
    → ∀{J}(A : Φ ⊢NeN⋆ J)
      -------------------------------------------
    → renameNeN (f ∘ g) A ≡ renameNeN f (renameNeN g A)
  renameNeN-comp g f (` x) = cong ` refl
  renameNeN-comp g f (A · x) =
    cong₂ _·_ (renameNeN-comp g f A) (renameNf-comp g f x)
  renameNeN-comp g f (μ B) =
    cong μ (trans (renameNf-cong _ _ ext-comp B)
                  (renameNf-comp (ext g) (ext f) B))

\end{code}

\begin{code}
embNf : ∀{Γ K} → Γ ⊢Nf⋆ K → Γ ⊢⋆ K
embNeN : ∀{Γ K} → Γ ⊢NeN⋆ K → Γ ⊢⋆ K

embNf (Π B)   = Π (embNf B)
embNf (A ⇒ B) = embNf A ⇒ embNf B
embNf (ƛ B)   = ƛ (embNf B)
embNf (ne B)  = embNeN B

embNeN (` x) = ` x
embNeN (A · B) = embNeN A · embNf B
embNeN (μ B)   = μ (embNf B)

\end{code}

\begin{code}
rename-embNeN : ∀ {Φ Ψ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → ∀ {J}
  → (n : Φ ⊢NeN⋆ J)
  → embNeN (renameNeN ρ n) ≡ rename ρ (embNeN n)

rename-embNf : ∀ {Φ Ψ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → ∀ {J}
  → (n : Φ ⊢Nf⋆ J)
  → embNf (renameNf ρ n) ≡ rename ρ (embNf n)
rename-embNf ρ (Π B) = cong Π (rename-embNf (ext ρ) B)
rename-embNf ρ (A ⇒ B) = cong₂ _⇒_ (rename-embNf ρ A) (rename-embNf ρ B)
rename-embNf ρ (ƛ B) = cong ƛ (rename-embNf (ext ρ) B)
rename-embNf ρ (ne n) = rename-embNeN ρ n

rename-embNeN ρ (` x) = refl
rename-embNeN ρ (n · n') = cong₂ _·_ (rename-embNeN ρ n) (rename-embNf ρ n')
rename-embNeN ρ (μ B) = cong μ (rename-embNf (ext ρ) B)
\end{code}
