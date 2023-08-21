module Type.NbE where

open import Context
open import Type.Core

open import Function
open import Data.Empty
open import Data.Sum.Base

infix  3 _⊢ᵗⁿᵉ_ _⊢ᵗⁿᶠ_ _⊨ᵗ_
infixl 9 _[_]ᵗ

mutual
  Starⁿᵉ : Conᵏ -> Set
  Starⁿᵉ Θ = Θ ⊢ᵗⁿᵉ ⋆

  Starⁿᶠ : Conᵏ -> Set
  Starⁿᶠ Θ = Θ ⊢ᵗⁿᶠ ⋆

  data _⊢ᵗⁿᵉ_ Θ : Kind -> Set where
    Varⁿᵉ : ∀ {σ} -> σ ∈ Θ -> Θ ⊢ᵗⁿᵉ σ
    _∙ⁿᵉ_ : ∀ {σ τ} -> Θ ⊢ᵗⁿᵉ σ ⇒ᵏ τ -> Θ ⊢ᵗⁿᶠ σ -> Θ ⊢ᵗⁿᵉ τ
    _⇒ⁿᵉ_ : Starⁿᵉ Θ -> Starⁿᵉ Θ -> Starⁿᵉ Θ
    πⁿᵉ   : ∀ σ -> Starⁿᵉ (Θ ▻ σ) -> Starⁿᵉ Θ
    μⁿᵉ   : ∀ {κ} -> Θ ⊢ᵗⁿᶠ (κ ⇒ᵏ ⋆) ⇒ᵏ κ ⇒ᵏ ⋆ -> Θ ⊢ᵗⁿᶠ κ -> Starⁿᵉ Θ

  data _⊢ᵗⁿᶠ_ Θ : Kind -> Set where
    Neⁿᶠ   : ∀ {σ} -> Θ ⊢ᵗⁿᵉ σ -> Θ ⊢ᵗⁿᶠ σ
    Lamⁿᶠ_ : ∀ {σ τ} -> Θ ▻ σ ⊢ᵗⁿᶠ τ -> Θ ⊢ᵗⁿᶠ σ ⇒ᵏ τ

mutual
  embᵗⁿᵉ : ∀ {Θ σ} -> Θ ⊢ᵗⁿᵉ σ -> Θ ⊢ᵗ σ
  embᵗⁿᵉ (Varⁿᵉ v) = Var v
  embᵗⁿᵉ (φ ∙ⁿᵉ α) = embᵗⁿᵉ φ ∙ embᵗⁿᶠ α
  embᵗⁿᵉ (α ⇒ⁿᵉ β) = embᵗⁿᵉ α ⇒ embᵗⁿᵉ β
  embᵗⁿᵉ (πⁿᵉ σ α) = π σ (embᵗⁿᵉ α)
  embᵗⁿᵉ (μⁿᵉ ψ α) = μ (embᵗⁿᶠ ψ) (embᵗⁿᶠ α)

  embᵗⁿᶠ : ∀ {Θ σ} -> Θ ⊢ᵗⁿᶠ σ -> Θ ⊢ᵗ σ
  embᵗⁿᶠ (Neⁿᶠ α)  = embᵗⁿᵉ α
  embᵗⁿᶠ (Lamⁿᶠ β) = Lam (embᵗⁿᶠ β)

mutual
  renᵗⁿᵉ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗⁿᵉ σ -> Ξ ⊢ᵗⁿᵉ σ
  renᵗⁿᵉ ι (Varⁿᵉ v) = Varⁿᵉ (renᵛ ι v)
  renᵗⁿᵉ ι (φ ∙ⁿᵉ α) = renᵗⁿᵉ ι φ ∙ⁿᵉ renᵗⁿᶠ ι α
  renᵗⁿᵉ ι (α ⇒ⁿᵉ β) = renᵗⁿᵉ ι α ⇒ⁿᵉ renᵗⁿᵉ ι β
  renᵗⁿᵉ ι (πⁿᵉ σ α) = πⁿᵉ σ (renᵗⁿᵉ (keep ι) α)
  renᵗⁿᵉ ι (μⁿᵉ ψ α) = μⁿᵉ (renᵗⁿᶠ ι ψ) (renᵗⁿᶠ ι α)

  renᵗⁿᶠ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗⁿᶠ σ -> Ξ ⊢ᵗⁿᶠ σ
  renᵗⁿᶠ ι (Neⁿᶠ α)  = Neⁿᶠ (renᵗⁿᵉ ι α)
  renᵗⁿᶠ ι (Lamⁿᶠ β) = Lamⁿᶠ (renᵗⁿᶠ (keep ι) β)

mutual
  _⊨ᵗ_ : Conᵏ -> Kind -> Set
  Θ ⊨ᵗ σ = Θ ⊢ᵗⁿᵉ σ ⊎ Kripke Θ σ

  Kripke : Conᵏ -> Kind -> Set
  Kripke Θ  ⋆       = ⊥
  Kripke Θ (σ ⇒ᵏ τ) = ∀ {Ξ} -> Θ ⊆ Ξ -> Ξ ⊨ᵗ σ -> Ξ ⊨ᵗ τ

Neˢ : ∀ {σ Θ} -> Θ ⊢ᵗⁿᵉ σ -> Θ ⊨ᵗ σ
Neˢ = inj₁

Varˢ : ∀ {σ Θ} -> σ ∈ Θ -> Θ ⊨ᵗ σ
Varˢ = Neˢ ∘ Varⁿᵉ

renᵗˢ : ∀ {σ Θ Δ} -> Θ ⊆ Δ -> Θ ⊨ᵗ σ -> Δ ⊨ᵗ σ
renᵗˢ          ι (inj₁ α)  = inj₁ (renᵗⁿᵉ ι α)
renᵗˢ {⋆}      ι (inj₂ ())
renᵗˢ {σ ⇒ᵏ τ} ι (inj₂ k)  = inj₂ λ κ -> k (κ ∘ ι)

readbackᵗ : ∀ {σ Θ} -> Θ ⊨ᵗ σ -> Θ ⊢ᵗⁿᶠ σ
readbackᵗ          (inj₁ α)  = Neⁿᶠ α
readbackᵗ {⋆}      (inj₂ ())
readbackᵗ {σ ⇒ᵏ τ} (inj₂ k)  = Lamⁿᶠ (readbackᵗ (k topᵒ (Varˢ vz)))

_∙ˢ_ : ∀ {Θ σ τ} -> Θ ⊨ᵗ σ ⇒ᵏ τ -> Θ ⊨ᵗ σ -> Θ ⊨ᵗ τ
inj₁ f ∙ˢ x = Neˢ (f ∙ⁿᵉ readbackᵗ x)
inj₂ k ∙ˢ x = k idᵒ x

groundⁿᵉ : ∀ {Θ} -> Θ ⊨ᵗ ⋆ -> Θ ⊢ᵗⁿᵉ ⋆
groundⁿᵉ (inj₁ α)  = α
groundⁿᵉ (inj₂ ())

environmentᵗˢ : Environment _⊨ᵗ_
environmentᵗˢ = record
  { varᵈ = Varˢ
  ; renᵈ = renᵗˢ
  }

module _ where
  open Environment environmentᵗˢ

  mutual
    evalᵗ : ∀ {Θ Ξ σ} -> Ξ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊨ᵗ σ
    evalᵗ ρ (Var v) = lookupᵉ v ρ
    evalᵗ ρ (Lam β) = inj₂ λ ι α -> evalᵗ (renᵉ ι ρ ▷ α) β
    evalᵗ ρ (φ ∙ α) = evalᵗ ρ φ ∙ˢ evalᵗ ρ α
    evalᵗ ρ (α ⇒ β) = inj₁ $ groundⁿᵉ (evalᵗ ρ α) ⇒ⁿᵉ groundⁿᵉ (evalᵗ ρ β)
    evalᵗ ρ (π σ α) = inj₁ $ πⁿᵉ σ ∘ groundⁿᵉ $ evalᵗ (keepᵉ ρ) α
    evalᵗ ρ (μ ψ α) = inj₁ $ μⁿᵉ (nfᵗ ρ ψ) (nfᵗ ρ α)

    nfᵗ : ∀ {Θ Ξ σ} -> Ξ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗⁿᶠ σ
    nfᵗ ρ = readbackᵗ ∘ evalᵗ ρ

  normalize : ∀ {Θ σ} -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ σ
  normalize = embᵗⁿᶠ ∘ nfᵗ idᵉ

_[_]ᵗ : ∀ {Θ σ τ} -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
β [ α ]ᵗ = normalize $ Lam β ∙ α
{-# DISPLAY normalize (Lam β ∙ α) = β [ α ]ᵗ #-}
