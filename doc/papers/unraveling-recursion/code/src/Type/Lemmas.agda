module Type.Lemmas where

open import Context
open import Type.Core

open import Function
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

foldlᶜ-▻-ε : ∀ {α} {A : Set α} -> (Θ : Con A) -> foldlᶜ _▻_ ε Θ ≡ Θ
foldlᶜ-▻-ε  ε      = refl
foldlᶜ-▻-ε (Γ ▻ σ) = cong (_▻ σ) (foldlᶜ-▻-ε Γ)

-- Same as `mapᶜ f (Γ ▻▻ Δ) ≡ mapᶜ f Γ ▻▻ mapᶜ f Δ`, but we fully inline the definitions,
-- because the REWRITE pragma requires that.
mapᶜ-▻▻
  : ∀ {α β} {A : Set α} {B : Set β} {f : A -> B} {Γ : Con A}
  -> ∀ Δ ->
      foldlᶜ (λ Ξ σ -> Ξ ▻ f σ) ε (foldlᶜ _▻_ Γ Δ)
    ≡ foldlᶜ _▻_ (foldlᶜ (λ Ξ σ -> Ξ ▻ f σ) ε Γ) (foldlᶜ (λ Ξ σ -> Ξ ▻ f σ) ε Δ)
mapᶜ-▻▻  ε      = refl
mapᶜ-▻▻ (Δ ▻ τ) = cong (_▻ _) (mapᶜ-▻▻ Δ)

keep-id : ∀ {α} {A : Set α} {Γ : Con A} {σ τ} -> (v : σ ∈ Γ ▻ τ) -> keep id v ≡ v
keep-id  vz    = refl
keep-id (vs v) = refl

keep-keep
  : ∀ {α} {A : Set α} {Γ Δ Ξ : Con A} {σ τ}
  -> (κ : Δ ⊆ Ξ) -> (ι : Γ ⊆ Δ) -> (v : σ ∈ Γ ▻ τ) -> keep κ (keep ι v) ≡ keep (κ ∘ ι) v
keep-keep κ ι  vz    = refl
keep-keep κ ι (vs v) = refl

dupl-keep-vs
  : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ τ}
  -> (ι : Γ ⊆ Δ) -> (v : σ ∈ Γ ▻ τ) -> dupl (keep (vs_ ∘ ι) v) ≡ keep ι v
dupl-keep-vs ι  vz    = refl
dupl-keep-vs ι (vs v) = refl

inject-foldr-poly
  : ∀ {α β γ} {A : Set α} {B : Set β} {yᶠ yᵍ}
  -> (C : B -> Set γ)
  -> (h : ∀ {yʰ} -> C yʰ -> C yʰ -> C yʰ)
  -> (g : C yᶠ -> C yᵍ)
  -> (∀ {y z} -> h (g y) (g z) ≡ g (h y z))
  -> (f : A -> C yᶠ)
  -> (Γ : Con A)
  -> (z : C yᶠ)
  -> g (foldrᶜ (h ∘ f) z Γ) ≡ foldrᶜ (h ∘ g ∘ f) (g z) Γ
inject-foldr-poly C h g dist f  ε      y = refl
inject-foldr-poly C h g dist f (Γ ▻ x) y
  rewrite dist {f x} {y} = inject-foldr-poly C h g dist f Γ (h (f x) y)

inject-foldr-mono
  : ∀ {α β} {A : Set α} {B : Set β}
  -> (h : B -> B -> B)
  -> (g : B -> B)
  -> (∀ {y z} -> h (g y) (g z) ≡ g (h y z))
  -> (f : A -> B)
  -> (Γ : Con A)
  -> (y : B)
  -> g (foldrᶜ (h ∘ f) y Γ) ≡ foldrᶜ (h ∘ g ∘ f) (g y) Γ
inject-foldr-mono h g dist f Γ y = inject-foldr-poly {B = ⊤} _ h g dist f Γ y

keep-eq
  : ∀ {α} {A : Set α} {Θ Ξ : Con A} {σ} (ι κ : Θ ⊆ Ξ)
  -> (∀ {τ} -> (v : τ ∈ Θ)     -> renᵛ       ι  v ≡ renᵛ       κ  v)
  -> (∀ {τ} -> (v : τ ∈ Θ ▻ σ) -> renᵛ (keep ι) v ≡ renᵛ (keep κ) v)
keep-eq ι κ q  vz    = refl
keep-eq ι κ q (vs v) = cong vs_ (q v)

renᵗ-ext
  : ∀ {Θ Ξ σ} (ι κ : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
  -> (∀ {τ} -> (v : τ ∈ Θ) -> renᵛ ι v ≡ renᵛ κ v)
  -> renᵗ ι α ≡ renᵗ κ α
renᵗ-ext ι κ (Var v) q = cong  Var (q v)
renᵗ-ext ι κ (Lam β) q = cong Lam_ (renᵗ-ext (keep ι) (keep κ) β (keep-eq ι κ q))
renᵗ-ext ι κ (φ ∙ α) q = cong₂ _∙_ (renᵗ-ext ι κ φ q) (renᵗ-ext ι κ α q)
renᵗ-ext ι κ (α ⇒ β) q = cong₂ _⇒_ (renᵗ-ext ι κ α q) (renᵗ-ext ι κ β q)
renᵗ-ext ι κ (π σ β) q = cong (π σ) (renᵗ-ext (keep ι) (keep κ) β (keep-eq ι κ q))
renᵗ-ext ι κ (μ ψ α) q = cong₂ μ (renᵗ-ext ι κ ψ q) (renᵗ-ext ι κ α q)

renᵗ-keep-keep
  : ∀ {Θ Ξ Ω σ τ} (κ : Ξ ⊆ Ω) (ι : Θ ⊆ Ξ) (β : Θ ▻ σ ⊢ᵗ τ)
  -> renᵗ (keep κ ∘ keep ι) β ≡ renᵗ (keep (κ ∘ ι)) β
renᵗ-keep-keep κ ι β = renᵗ-ext (keep κ ∘ keep ι) (keep (κ ∘ ι)) β λ
  {  vz    -> refl
  ; (vs v) -> refl
  }

renᵗ-∘
  : ∀ {Θ Ξ Ω σ} (κ : Ξ ⊆ Ω) (ι : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
  -> renᵗ κ (renᵗ ι α) ≡ renᵗ (κ ∘ ι) α
renᵗ-∘ κ ι (Var v) = refl
renᵗ-∘ κ ι (Lam β) = cong Lam_ (trans (renᵗ-∘ (keep κ) (keep ι) β) (renᵗ-keep-keep κ ι β))
renᵗ-∘ κ ι (f ∙ α) = cong₂ _∙_ (renᵗ-∘ κ ι f) (renᵗ-∘ κ ι α)
renᵗ-∘ κ ι (α ⇒ β) = cong₂ _⇒_  (renᵗ-∘ κ ι α) (renᵗ-∘ κ ι β)
renᵗ-∘ κ ι (π σ β) = cong (π σ) (trans (renᵗ-∘ (keep κ) (keep ι) β) (renᵗ-keep-keep κ ι β))
renᵗ-∘ κ ι (μ ψ α) = cong₂ μ (renᵗ-∘ κ ι ψ) (renᵗ-∘ κ ι α)

renᵗ-keep-id
  : ∀ {Θ σ τ} (β : Θ ▻ σ ⊢ᵗ τ)
  -> renᵗ (keep id) β ≡ renᵗ id β
renᵗ-keep-id β = renᵗ-ext (keep id) id β λ
  {  vz    -> refl
  ; (vs v) -> refl
  }

renᵗ-id : ∀ {Θ σ} (α : Θ ⊢ᵗ σ) -> renᵗ id α ≡ α
renᵗ-id (Var v) = refl
renᵗ-id (Lam β) = cong Lam_ (trans (renᵗ-keep-id β) (renᵗ-id β))
renᵗ-id (φ ∙ α) = cong₂ _∙_ (renᵗ-id φ) (renᵗ-id α)
renᵗ-id (α ⇒ β) = cong₂ _⇒_ (renᵗ-id α) (renᵗ-id β)
renᵗ-id (π σ β) = cong (π σ) (trans (renᵗ-keep-id β) (renᵗ-id β))
renᵗ-id (μ ψ α) = cong₂ μ (renᵗ-id ψ) (renᵗ-id α)

module EnvironmentLemmas
    {α β} {A : Set α} {_◆_ : Con A -> A -> Set β}
    (environment : Environment _◆_) where
  open Environment environment

  keepᵉ-eq
    : ∀ {Θ Ξ : Con A} {σ} (ρ χ : Ξ ⊢ᵉ Θ)
    -> (∀ {τ} -> (v : τ ∈ Θ)     -> lookupᵉ v        ρ  ≡ lookupᵉ v        χ )
    -> (∀ {τ} -> (v : τ ∈ Θ ▻ σ) -> lookupᵉ v (keepᵉ ρ) ≡ lookupᵉ v (keepᵉ χ))
  keepᵉ-eq ρ χ q  vz    = refl
  keepᵉ-eq ρ χ q (vs v) = cong (renᵈ vs_) (q v)

module _ where
  open TypeEnv
  open EnvironmentLemmas environmentᵗ

  subᵗ-ext
    : ∀ {Θ Ξ σ} (ρ χ : Ξ ⊢ᵗᵉ Θ) (α : Θ ⊢ᵗ σ)
    -> (∀ {τ} -> (v : τ ∈ Θ) -> lookupᵉ v ρ ≡ lookupᵉ v χ)
    -> subᵗ ρ α ≡ subᵗ χ α
  subᵗ-ext ρ χ (Var v) q = q v
  subᵗ-ext ρ χ (Lam β) q = cong Lam_ (subᵗ-ext (keepᵉ ρ) (keepᵉ χ) β (keepᵉ-eq ρ χ q))
  subᵗ-ext ρ χ (φ ∙ α) q = cong₂ _∙_ (subᵗ-ext ρ χ φ q) (subᵗ-ext ρ χ α q)
  subᵗ-ext ρ χ (α ⇒ β) q = cong₂ _⇒_ (subᵗ-ext ρ χ α q) (subᵗ-ext ρ χ β q)
  subᵗ-ext ρ χ (π σ β) q = cong (π σ) (subᵗ-ext (keepᵉ ρ) (keepᵉ χ) β (keepᵉ-eq ρ χ q))
  subᵗ-ext ρ χ (μ ψ α) q = cong₂ μ (subᵗ-ext ρ χ ψ q) (subᵗ-ext ρ χ α q)

  subᵗ-keepᵉ-keep
    : ∀ {Θ Ξ Ω σ τ} (ρ : Ω ⊢ᵗᵉ Ξ) (ι : Θ ⊆ Ξ) (β : Θ ▻ σ ⊢ᵗ τ)
    -> subᵗ (keepᵉ ρ ∘ᵉ keep ι) β ≡ subᵗ (keepᵉ (ρ ∘ᵉ ι)) β
  subᵗ-keepᵉ-keep ρ ι β = subᵗ-ext (keepᵉ ρ ∘ᵉ keep ι) (keepᵉ (ρ ∘ᵉ ι)) β λ
    {  vz    -> refl
    ; (vs v) -> refl
    }

  subᵗ-renᵗ
    : ∀ {Θ Ξ Ω σ} (ρ : Ω ⊢ᵗᵉ Ξ) (ι : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
    -> subᵗ ρ (renᵗ ι α) ≡ subᵗ (ρ ∘ᵉ ι) α
  subᵗ-renᵗ ρ ι (Var v) = refl
  subᵗ-renᵗ ρ ι (Lam β) = cong Lam_ (trans (subᵗ-renᵗ (keepᵉ ρ) (keep ι) β) (subᵗ-keepᵉ-keep ρ ι β))
  subᵗ-renᵗ ρ ι (φ ∙ α) = cong₂ _∙_ (subᵗ-renᵗ ρ ι φ) (subᵗ-renᵗ ρ ι α)
  subᵗ-renᵗ ρ ι (α ⇒ β) = cong₂ _⇒_ (subᵗ-renᵗ ρ ι α) (subᵗ-renᵗ ρ ι β)
  subᵗ-renᵗ ρ ι (π σ β) = cong (π σ) (trans (subᵗ-renᵗ (keepᵉ ρ) (keep ι) β) (subᵗ-keepᵉ-keep ρ ι β))
  subᵗ-renᵗ ρ ι (μ ψ α) = cong₂ μ (subᵗ-renᵗ ρ ι ψ) (subᵗ-renᵗ ρ ι α)

  subᵗ-keepᵉ-idᵉ
    : ∀ {Θ σ τ} (β : Θ ▻ σ ⊢ᵗ τ)
    -> subᵗ (keepᵉ idᵉ) β ≡ subᵗ idᵉ β
  subᵗ-keepᵉ-idᵉ β = subᵗ-ext (keepᵉ idᵉ) idᵉ β λ
    {  vz    -> refl
    ; (vs v) -> refl
    }

  subᵗ-idᵉ
    : ∀ {Θ σ} (α : Θ ⊢ᵗ σ)
    -> subᵗ idᵉ α ≡ α
  subᵗ-idᵉ (Var v) = refl
  subᵗ-idᵉ (Lam β) = cong Lam_ (trans (subᵗ-keepᵉ-idᵉ β) (subᵗ-idᵉ β))
  subᵗ-idᵉ (φ ∙ α) = cong₂ _∙_ (subᵗ-idᵉ φ) (subᵗ-idᵉ α)
  subᵗ-idᵉ (α ⇒ β) = cong₂ _⇒_ (subᵗ-idᵉ α) (subᵗ-idᵉ β)
  subᵗ-idᵉ (π σ β) = cong (π σ) (trans (subᵗ-keepᵉ-idᵉ β) (subᵗ-idᵉ β))
  subᵗ-idᵉ (μ ψ α) = cong₂ μ (subᵗ-idᵉ ψ) (subᵗ-idᵉ α)

  subᵗ-keepᵉ-Var
    : ∀ {Θ Ξ σ τ} (ι : Θ ⊆ Ξ) (β : Θ ▻ σ ⊢ᵗ τ)
    -> subᵗ (keepᵉ (PackEnv (Var ∘ ι))) β ≡ subᵗ (PackEnv (Var ∘ keep ι)) β
  subᵗ-keepᵉ-Var ι β = subᵗ-ext (keepᵉ (PackEnv (Var ∘ ι))) (PackEnv (Var ∘ keep ι)) β λ
    {  vz    -> refl
    ; (vs v) -> refl
    }

  subᵗ-Var
    : ∀ {Θ Ξ σ} (ι : Θ ⊆ Ξ) (α : Θ ⊢ᵗ σ)
    -> subᵗ (PackEnv (Var ∘ ι)) α ≡ renᵗ ι α
  subᵗ-Var ι (Var v) = refl
  subᵗ-Var ι (Lam β) = cong Lam_ (trans (subᵗ-keepᵉ-Var ι β) (subᵗ-Var (keep ι) β))
  subᵗ-Var ι (φ ∙ α) = cong₂ _∙_ (subᵗ-Var ι φ) (subᵗ-Var ι α)
  subᵗ-Var ι (α ⇒ β) = cong₂ _⇒_ (subᵗ-Var ι α) (subᵗ-Var ι β)
  subᵗ-Var ι (π σ β) = cong (π σ) (trans (subᵗ-keepᵉ-Var ι β) (subᵗ-Var (keep ι) β))
  subᵗ-Var ι (μ ψ α) = cong₂ μ (subᵗ-Var ι ψ) (subᵗ-Var ι α)

inject-foldr-⇒-renᵗ
  : ∀ {Θ Ξ Ω} {f : Star Θ -> Star Ξ}
  -> ∀ Δ
  -> (ι : Ξ ⊆ Ω)
  -> (β : Star Ξ)
  -> renᵗ ι (conToTypeBy f Δ β) ≡ conToTypeBy (renᵗ ι ∘ f) Δ (renᵗ ι β)
inject-foldr-⇒-renᵗ Δ ι β = inject-foldr-poly Star _⇒_ (renᵗ ι) refl _ Δ β

inject-foldr-⇒-subᵗ
  : ∀ {Θ Ξ Ω} {f : Star Θ -> Star Ξ}
  -> ∀ Δ
  -> (ρ : Ω TypeEnv.⊢ᵉ Ξ)
  -> (β : Star Ξ)
  -> subᵗ ρ (conToTypeBy f Δ β) ≡ conToTypeBy (subᵗ ρ ∘ f) Δ (subᵗ ρ β)
inject-foldr-⇒-subᵗ Δ ρ β = inject-foldr-poly Star _⇒_ (subᵗ ρ) refl _ Δ β
