\begin{code}
module Type.Normal where
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
open import Type.Value
open import Type.RenamingSubstitution

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)


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

  μ : ∀{φ}
    → φ ,⋆ * ⊢Nf⋆ *
      -----------
    → φ ⊢Nf⋆ *

  ne : ∀{φ K} -- if it was at kind * it would be βη-normal forms
    → φ ⊢NeN⋆ K
      --------
    → φ ⊢Nf⋆ K
\end{code}

\begin{code}
{-# TERMINATING #-}
readbackNf  : ∀{φ K} → φ ⊢V⋆ K → φ ⊢Nf⋆ K
readbackNeN : ∀{φ K} → φ ⊢Ne⋆ K → φ ⊢NeN⋆ K

readbackNf (Π t vs) = Π (readbackNf (eval t (extEnv vs)))
readbackNf (A ⇒ B)  = readbackNf A ⇒ readbackNf B
readbackNf (ƛ t vs) = ƛ (readbackNf (eval t (extEnv vs)))
readbackNf (μ t vs) = μ (readbackNf (eval t (extEnv vs)))
readbackNf (ne n)   = ne (readbackNeN n)

readbackNeN (` x)    = ` x
readbackNeN (n · n') = readbackNeN n · readbackNf n'
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = readbackNf (eval t idEnv)
\end{code}

\begin{code}
embNf : ∀{Γ K} → Γ ⊢Nf⋆ K → Γ ⊢⋆ K
embNeN : ∀{Γ K} → Γ ⊢NeN⋆ K → Γ ⊢⋆ K

embNf (Π B)   = Π (embNf B)
embNf (A ⇒ B) = embNf A ⇒ embNf B
embNf (ƛ B)   = ƛ (embNf B)
embNf (μ B)   = μ (embNf B)
embNf (ne B)  = embNeN B

embNeN (` x) = ` x
embNeN (A · B) = embNeN A · embNf B
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = nf (embNf A [ embNf B ])
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
renameNf ρ (μ B)   = μ (renameNf (ext ρ) B)
renameNf ρ (ne A)  = ne (renameNeN ρ A)

renameNeN ρ (` x) = ` (ρ x)
renameNeN ρ (A · x) = renameNeN ρ A · renameNf ρ x
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
  cong Π (renameNf-cong (ext f) (ext g) (ext-cong f g p) A)
renameNf-cong f g p (A ⇒ B) =
  cong₂ _⇒_ (renameNf-cong f g p A) (renameNf-cong f g p B)
renameNf-cong f g p (ƛ A)   =
  cong ƛ (renameNf-cong (ext f) (ext g) (ext-cong f g p) A)
renameNf-cong f g p (μ A)   =
  cong μ (renameNf-cong (ext f) (ext g) (ext-cong f g p) A)
renameNf-cong f g p (ne A) = cong ne (renameNeN-cong f g p A)

renameNeN-cong f g p (` x)   = cong ` (p x)
renameNeN-cong f g p (A · B) =
  cong₂ _·_ (renameNeN-cong f g p A) (renameNf-cong f g p B)
\end{code}

\begin{code}
mutual
  renameNf-comp : ∀{Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
    → ∀{J}(A : Φ ⊢Nf⋆ J)
      -------------------------------------------
    → renameNf (f ∘ g) A ≡ renameNf f (renameNf g A)
  renameNf-comp g f (Π B) =
    cong Π (trans (renameNf-cong _ _ (ext-comp g f) B)
                  (renameNf-comp (ext g) (ext f) B))
  renameNf-comp g f (A ⇒ B) =
    cong₂ _⇒_ (renameNf-comp g f A) (renameNf-comp g f B)
  renameNf-comp g f (ƛ B) = 
    cong ƛ (trans (renameNf-cong _ _ (ext-comp g f) B)
                  (renameNf-comp (ext g) (ext f) B))
  renameNf-comp g f (μ B) =
    cong μ (trans (renameNf-cong _ _ (ext-comp g f) B)
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
\end{code}

\begin{code}
{-# TERMINATING #-}
rename-readbackNf : ∀ {Φ Ψ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → ∀{K}(v : Φ ⊢V⋆ K)
  → readbackNf (renameV ρ v) ≡ renameNf ρ (readbackNf v)

rename-readbackNeN : ∀ {Φ Ψ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → ∀{K}(n : Φ ⊢Ne⋆ K)
  → readbackNeN (renameNe ρ n) ≡ renameNeN ρ (readbackNeN n)

rename-readbackNf ρ (Π B vs) =
  cong Π
       (trans (cong readbackNf
                    (trans (cong (eval B)
                                 (cong (_,⋆ ne (` Z))
                                       (trans (sym (renameE-comp ρ S vs))
                                              (renameE-comp S (ext ρ) vs))))
                           (renameV-eval B (extEnv vs) (ext ρ))))
              (rename-readbackNf (ext ρ) (eval B (extEnv vs))))
rename-readbackNf ρ (A ⇒ B)  =
 cong₂ _⇒_ (rename-readbackNf ρ A) (rename-readbackNf ρ B)
rename-readbackNf ρ (ƛ B vs) = 
  cong ƛ
       (trans (cong readbackNf
                    (trans (cong (eval B)
                                 (cong (_,⋆ ne (` Z))
                                       (trans (sym (renameE-comp ρ S vs))
                                              (renameE-comp S (ext ρ) vs))))
                           (renameV-eval B (extEnv vs) (ext ρ))))
              (rename-readbackNf (ext ρ) (eval B (extEnv vs))))
rename-readbackNf ρ (μ B vs) =
  cong μ
       (trans (cong readbackNf
                    (trans (cong (eval B)
                                 (cong (_,⋆ ne (` Z))
                                       (trans (sym (renameE-comp ρ S vs))
                                              (renameE-comp S (ext ρ) vs))))
                           (renameV-eval B (extEnv vs) (ext ρ))))
              (rename-readbackNf (ext ρ) (eval B (extEnv vs))))
rename-readbackNf ρ (ne A)   = cong ne (rename-readbackNeN ρ A)

rename-readbackNeN ρ (` x) = refl
rename-readbackNeN ρ (n · n') =
  cong₂ _·_ (rename-readbackNeN ρ n) (rename-readbackNf ρ n')
\end{code}
