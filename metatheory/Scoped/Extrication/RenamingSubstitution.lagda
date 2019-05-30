\begin{code}
module Scoped.Extrication.RenamingSubstitution where
\end{code}

erasure commutes with renaming/substitution

\begin{code}
open import Type
open import Type.BetaNormal
open import Data.Nat
open import Data.Fin
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality as Eq
open import Algorithmic as A
open import Type.RenamingSubstitution as T
open import Type.BetaNormal
open import Scoped
open import Scoped.Extrication
open import Algorithmic.RenamingSubstitution as AS
open import Scoped.RenamingSubstitution as SS
open import Builtin

-- type renamings

open import Data.Product renaming (_,_ to _,,_)

backVar : ∀{Γ} → Fin (len⋆ Γ) → Σ Kind λ J → Γ ∋⋆ J
backVar {Γ ,⋆ K} zero    = K ,, Z
backVar {Γ ,⋆ K} (suc i) = let J ,, α = backVar i in J ,, S α

lem-backVar₁ : ∀{Γ J}(α : Γ ∋⋆ J) → proj₁ (backVar (extricateVar⋆ α)) ≡ J
lem-backVar₁ Z = refl
lem-backVar₁ (S α) = lem-backVar₁ α

lem-S : ∀{Φ K J J'} → (p : J ≡ J') → (α : Φ ∋⋆ J)
  → S (Eq.subst (Φ ∋⋆_) p α) ≡ Eq.subst (Φ ,⋆ K ∋⋆_) p (S α)
lem-S refl α = refl

lem-backVar : ∀{Γ J}(α : Γ ∋⋆ J)
  → Eq.subst (Γ ∋⋆_) (lem-backVar₁ α) (proj₂ (backVar (extricateVar⋆ α))) ≡ α
lem-backVar Z = refl
lem-backVar (S α) = trans
  (sym (lem-S (lem-backVar₁ α) (proj₂ (backVar (extricateVar⋆ α)))))
  (cong S (lem-backVar α))

extricateRenNf⋆ : ∀{Γ Δ}(ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) 
  → Ren⋆ (len⋆ Γ) (len⋆ Δ)
extricateRenNf⋆ ρ⋆ x = extricateVar⋆ (ρ⋆ (proj₂ (backVar x)))



{-
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ zero = extricateVar⋆ (ρ⋆ Z)
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ (suc α) = extricateRenNf⋆ (ρ⋆ ∘ S) α
-}

{-
ren-extricateVar⋆ : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → extricateRenNf⋆ ρ⋆ (extricateVar⋆ α) ≡ extricateVar⋆ (ρ⋆ α)
ren-extricateVar⋆ ρ⋆ Z     = ? -- refl
ren-extricateVar⋆ ρ⋆ (S α) = ren-extricateVar⋆ (ρ⋆ ∘ S) α


extricateRenNf⋆-comp : ∀{B Γ Δ}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) (ρ⋆' : ∀ {J} → B ∋⋆ J → Γ ∋⋆ J)
  → (α : Fin (len⋆ B))
  → extricateRenNf⋆ ρ⋆ (extricateRenNf⋆ ρ⋆' α) ≡ extricateRenNf⋆ (ρ⋆ ∘ ρ⋆') α
extricateRenNf⋆-comp {B ,⋆ K} ρ⋆ ρ⋆' zero    = ren-extricateVar⋆ ρ⋆ (ρ⋆' Z)
extricateRenNf⋆-comp {B ,⋆ K} ρ⋆ ρ⋆' (suc α) =
  extricateRenNf⋆-comp ρ⋆ (ρ⋆' ∘ S) α

lift⋆-ext : ∀{Γ Δ J K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ,⋆ K ∋⋆ J)
  → lift⋆ (extricateRenNf⋆ ρ⋆) (extricateVar⋆ α) ≡ extricateVar⋆ (T.ext ρ⋆ α)
lift⋆-ext ρ⋆ Z = refl
lift⋆-ext ρ⋆ (S α) = cong suc (ren-extricateVar⋆ ρ⋆ α)
-}
lift⋆-ext' : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Fin (len⋆ (Γ ,⋆ K)))
  → lift⋆ (extricateRenNf⋆ ρ⋆) α ≡ extricateRenNf⋆ (T.ext ρ⋆ {K = K}) α -- 
lift⋆-ext' ρ⋆ zero = refl
lift⋆-ext' ρ⋆ (suc α) = refl

ren-extricateNf⋆ :  ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢Nf⋆ J)
  → ren⋆ (extricateRenNf⋆ ρ⋆) (extricateNf⋆ A) ≡ extricateNf⋆ (renameNf ρ⋆ A)

lem-extricateVar⋆ :  ∀{Γ Δ J J'}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → (p : J ≡ J')
  → extricateVar⋆ (ρ⋆ α) ≡ extricateVar⋆ (ρ⋆ (Eq.subst (Γ ∋⋆_) p α))
lem-extricateVar⋆ ρ⋆ α refl = refl

ren-extricateNe⋆ :  ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢NeN⋆ J)
  → ren⋆ (extricateRenNf⋆ ρ⋆) (extricateNe⋆ A) ≡ extricateNe⋆ (renameNeN ρ⋆ A)
ren-extricateNe⋆ ρ⋆ (` x)   = cong
  `
  (trans (lem-extricateVar⋆ ρ⋆ (proj₂ (backVar (extricateVar⋆ x))) (lem-backVar₁ x))
  (cong (extricateVar⋆ ∘ ρ⋆) (lem-backVar x)))
ren-extricateNe⋆ ρ⋆ (A · B) =
  cong₂ _·_ (ren-extricateNe⋆ ρ⋆ A) (ren-extricateNf⋆ ρ⋆ B)
ren-extricateNe⋆ ρ⋆ μ1      = refl

ren-extricateNf⋆ ρ⋆ (Π x A)  =
  cong (Π x (extricateK _))
       (trans (ren⋆-cong (lift⋆-ext' ρ⋆) (extricateNf⋆ A))
              (ren-extricateNf⋆ (T.ext ρ⋆) A))
ren-extricateNf⋆ ρ⋆ (A ⇒ B)  =
  cong₂ _⇒_ (ren-extricateNf⋆ ρ⋆ A) (ren-extricateNf⋆ ρ⋆ B)
ren-extricateNf⋆ ρ⋆ (ƛ x A)  =
  cong (ƛ x (extricateK _))
       (trans (ren⋆-cong (lift⋆-ext' ρ⋆) (extricateNf⋆ A)) (ren-extricateNf⋆ (T.ext ρ⋆) A))
ren-extricateNf⋆ ρ⋆ (ne A)   = ren-extricateNe⋆ ρ⋆ A
ren-extricateNf⋆ ρ⋆ (con c)  = refl

{-
-- term level renamings

extricateRen : ∀{Φ Ψ Γ Δ}(ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J) →
  (ρ : ∀{J}{A : Φ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → SS.Ren (len Γ) (len Δ)
extricateRen {Γ = Γ ,⋆ J} {Δ} ρ⋆ ρ (T x) = extricateRen
  (ρ⋆ ∘ S)
  (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renameNf-comp A)) (ρ (T x)))
  x
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ Z     = extricateVar (ρ Z)
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ (S x) = extricateRen ρ⋆ (ρ ∘ S) x
-}



-- these are the two properties of extrication/ren/sub needed to define
-- extricate—→

postulate
  lem[] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}(N : Γ , A ⊢ B)(W : Γ ⊢ A)
    → extricate N SS.[ extricate W ] ≡ extricate (N AS.[ W ])

  lem[]⋆ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}(N : Γ ,⋆ K ⊢ B)(A : Φ ⊢Nf⋆ K)
    → extricate N SS.[ extricateNf⋆ A ]⋆ ≡ extricate (N AS.[ A ]⋆)
\end{code}
