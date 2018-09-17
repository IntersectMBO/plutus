\begin{code}
module Type.BSN where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _⊢V⋆_
\end{code}

## Imports

\begin{code}
open import Function
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)


open import Type
open import Type.RenamingSubstitution
open import Type.Equality
\end{code}

## Type Values


\begin{code}
data _⊢V⋆_ : Ctx⋆ → Kind → Set

Env⋆ : Ctx⋆ → Ctx⋆ → Set
Env⋆ Δ Γ = ∀ {J} → Γ ∋⋆ J → Δ ⊢V⋆ J

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢Ne⋆ (K ⇒ J)
    → Φ ⊢V⋆ K
      ------
    → Φ ⊢Ne⋆ J


data _⊢V⋆_ where

  Π : ∀ {Φ Ψ K}
    → Ψ ,⋆ K ⊢⋆ *
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢V⋆ *
    → Φ ⊢V⋆ *
      ------
    → Φ ⊢V⋆ *

  ƛ :  ∀ {Φ Ψ K J}
    → Ψ ,⋆ K ⊢⋆ J
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ (K ⇒ J)

  μ : ∀{φ Ψ}
    → Ψ ,⋆ * ⊢⋆ *
    → Env⋆ φ Ψ
      -----------
    → φ ⊢V⋆ *

  ne : ∀{φ K}
    → φ  ⊢Ne⋆ K
      -----------
    → φ ⊢V⋆ K
\end{code}

\begin{code}
_,,⋆_ : ∀{Δ Γ} → (σ : Env⋆ Δ Γ) → ∀{K}(A : Δ ⊢V⋆ K) → Env⋆ Δ (Γ ,⋆ K)
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
{-# TERMINATING #-}
eval : ∀{Ψ φ J} → Ψ ⊢⋆ J → Env⋆ φ Ψ → φ ⊢V⋆ J
_·V_ : ∀{φ J K} → φ ⊢V⋆ (J ⇒ K) → φ ⊢V⋆ J → φ ⊢V⋆ K
eval (` x)   vs = vs x
eval (Π t)   vs = Π t vs
eval (t ⇒ u) vs = eval t vs ⇒ eval u vs
eval (t · u) vs = eval t vs ·V eval u vs
eval (μ t)   vs = μ t vs
eval (ƛ t)   vs = ƛ t vs

ƛ t vs ·V v = eval t (vs ,,⋆ v)
ne n   ·V v = ne (n · v)
\end{code}

\begin{code}
renameNe : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J)

renameEnv : ∀{Φ Ψ Θ}
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  (g : Env⋆ Ψ Φ )
  → Env⋆  Θ Φ

renameV : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢V⋆ J → Ψ ⊢V⋆ J)
renameV ρ (Π B vs) = Π B (renameEnv ρ vs)
renameV ρ (A ⇒ B)  = renameV ρ A ⇒ renameV ρ B
renameV ρ (ƛ B vs) = ƛ B (renameEnv ρ vs)
renameV ρ (μ B vs) = μ B (renameEnv ρ vs)
renameV ρ (ne n)   = ne (renameNe ρ n)

renameNe ρ (` x) = ` (ρ x)
renameNe ρ (n · v) = renameNe ρ n · renameV ρ v

renameEnv f g x = renameV f (g x)
\end{code}

\begin{code}
weakenV : ∀ {Φ J K}
  → Φ ⊢V⋆ J
    -------------
  → Φ ,⋆ K ⊢V⋆ J
weakenV = renameV S
\end{code}

\begin{code}
weakenEnv : ∀ {Φ K ψ}
  → Env⋆ Φ  ψ
    -------------
  → Env⋆ (Φ ,⋆ K) ψ
weakenEnv = renameEnv S
\end{code}

\begin{code}
extEnv : ∀ {Φ Ψ K} → Env⋆ Φ Ψ
    -----------------------
  → Env⋆ (Φ ,⋆ K) (Ψ ,⋆ K)
extEnv ρ = weakenEnv ρ ,,⋆ ne (` Z)
\end{code}

\begin{code}
idEnv : ∀{Γ} → Env⋆ Γ Γ
idEnv  = ne ∘ `
\end{code}

\begin{code}
_⟦_⟧ : ∀{ϕ J K} → ϕ ,⋆ K ⊢⋆ J → ϕ ⊢V⋆ K → ϕ ⊢V⋆ J
t ⟦ v ⟧ = eval t (idEnv ,,⋆ v)
\end{code}

\begin{code}
open import Type.Normal

open import Data.Unit
open import Data.Product
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
{-
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
                                       (trans ? -- (sym (renameE-comp ρ S vs))
                                              ?))) -- (renameE-comp S (ext ρ) vs))))
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
-}
\end{code}

A partial equivalance relation for values
\begin{code}
_∋_∼_ : ∀{Γ} K → Γ ⊢V⋆ K → Γ ⊢V⋆ K → Set
* ∋ x ∼ y = readbackNf x ≡ readbackNf y
(K ⇒ J) ∋ f ∼ g =
  ∀{Δ}(ρ : ∀{J} → _ ∋⋆ J → Δ ∋⋆ J){v v' : Δ ⊢V⋆ K}
  → K ∋ v ∼ v'
  → J ∋ (renameV ρ f ·V v) ∼ (renameV ρ g ·V v)   
\end{code}
