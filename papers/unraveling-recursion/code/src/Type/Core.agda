module Type.Core where

open import Context

open import Function

infix  3 _⊢ᵗ_
infixr 6 _⇒ᵏ_ _⇒_
infixl 7 _∙_

-- | A `Kind` is either a star or an arrow.
data Kind : Set where
  ⋆    : Kind
  _⇒ᵏ_ : Kind -> Kind -> Kind

-- | Kind contexts.
Conᵏ : Set
Conᵏ = Con Kind

mutual
  -- | Types of kind `⋆`.
  Star : Conᵏ -> Set
  Star Θ = Θ ⊢ᵗ ⋆

  -- | A type is defined in a context and has a kind.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var  : ∀ {σ} -> (v : σ ∈ Θ) -> Θ ⊢ᵗ σ
    Lam_ : ∀ {σ τ} -> (β : Θ ▻ σ ⊢ᵗ τ) -> Θ ⊢ᵗ σ ⇒ᵏ τ
    _∙_  : ∀ {σ τ} -> (φ : Θ ⊢ᵗ σ ⇒ᵏ τ) -> (α : Θ ⊢ᵗ σ) -> Θ ⊢ᵗ τ
    _⇒_  : (α : Star Θ) -> (β : Star Θ) -> Star Θ
    π    : ∀ σ -> (β : Star (Θ ▻ σ)) -> Star Θ
    μ    : ∀ {κ} -> (ψ : Θ ⊢ᵗ (κ ⇒ᵏ ⋆) ⇒ᵏ κ ⇒ᵏ ⋆) -> (α : Θ ⊢ᵗ κ) -> Star Θ

-- | Closed types.
Type⁽⁾ : Kind -> Set
Type⁽⁾ σ = ε ⊢ᵗ σ

-- | Closed types that can be used in any context.
Type⁺ : Kind -> Set
Type⁺ σ = ∀ {Γ} -> Γ ⊢ᵗ σ

Star⁺ : Set
Star⁺ = Type⁺ ⋆

bindᵗ : ∀ {Θ σ τ} -> Θ ⊢ᵗ σ -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ τ
bindᵗ α β = (Lam β) ∙ α

-- | Expand the context that a type is defined in, but do not change anything in the type
-- (including variables).
wkᵗ : ∀ {Θ Ξ σ} -> Ξ ⊢ᵗ σ -> Θ ▻▻ Ξ ⊢ᵗ σ
wkᵗ (Var v) = Var (wkᵛ v)
wkᵗ (Lam β) = Lam (wkᵗ β)
wkᵗ (φ ∙ α) = wkᵗ φ ∙ wkᵗ α
wkᵗ (α ⇒ β) = wkᵗ α ⇒ wkᵗ β
wkᵗ (π σ β) = π σ (wkᵗ β)
wkᵗ (μ ψ α) = μ (wkᵗ ψ) (wkᵗ α)

-- | Lift a closed type to any context.
wk⁺ : ∀ {σ} -> Type⁽⁾ σ -> Type⁺ σ
wk⁺ α = wkᵗ α

-- | Rename a type.
renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v) = Var (renᵛ ι v)
renᵗ ι (Lam β) = Lam (renᵗ (keep ι) β)
renᵗ ι (φ ∙ α) = renᵗ ι φ ∙ renᵗ ι α
renᵗ ι (α ⇒ β) = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ α) = π σ (renᵗ (keep ι) α)
renᵗ ι (μ ψ α) = μ (renᵗ ι ψ) (renᵗ ι α)

-- | Extend the context of a type by another context and increase all variables as appropriate.
shiftᵗⁿ : ∀ {Θ σ} Ξ -> Θ ⊢ᵗ σ -> Θ ▻▻ Ξ ⊢ᵗ σ
shiftᵗⁿ Ξ = renᵗ (extʳ Ξ)

-- | Increase all variables in a type by one.
shiftᵗ : ∀ {Θ σ τ} -> Θ ⊢ᵗ σ -> Θ ▻ τ ⊢ᵗ σ
shiftᵗ = shiftᵗⁿ (ε ▻ _)

unshiftᵗ : ∀ {Θ σ τ} -> Θ ▻ σ ▻ σ ⊢ᵗ τ -> Θ ▻ σ ⊢ᵗ τ
unshiftᵗ = renᵗ dupl

shiftᶜⁿ : ∀ {Θ σ} Ξ -> Con (Θ ⊢ᵗ σ) -> Con (Θ ▻▻ Ξ ⊢ᵗ σ)
shiftᶜⁿ Ξ = mapᶜ (shiftᵗⁿ Ξ)

shiftᶜ : ∀ {Θ σ τ} -> Con (Θ ⊢ᵗ σ) -> Con (Θ ▻ τ ⊢ᵗ σ)
shiftᶜ = mapᶜ shiftᵗ

environmentᵗ : Environment _⊢ᵗ_
environmentᵗ = record
  { varᵈ = Var
  ; renᵈ = renᵗ
  }

module TypeEnv = Environment environmentᵗ

_⊢ᵗᵉ_ = TypeEnv._⊢ᵉ_

module _ where
  open TypeEnv

  subᵗ : ∀ {Θ Ξ σ} -> Ξ ⊢ᵗᵉ Θ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
  subᵗ ρ (Var v) = lookupᵉ v ρ
  subᵗ ρ (Lam β) = Lam (subᵗ (keepᵉ ρ) β)
  subᵗ ρ (φ ∙ α) = subᵗ ρ φ ∙ subᵗ ρ α
  subᵗ ρ (α ⇒ β) = subᵗ ρ α ⇒ subᵗ ρ β
  subᵗ ρ (π σ β) = π σ (subᵗ (keepᵉ ρ) β)
  subᵗ ρ (μ ψ α) = μ (subᵗ ρ ψ) (subᵗ ρ α)

  _<_>ᵗ : ∀ {Θ σ τ} -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ
  β < α >ᵗ = subᵗ (topᵉ α) β

-- | Right-fold a context with `_⇒ᵏ_ ∘ f`.
--
-- > conToKindBy f (ε ▻ σ₁ ▻ … ▻ σₙ) τ = f σ₁ ⇒ᵏ … ⇒ᵏ f σₙ ⇒ᵏ τ
conToKindBy : ∀ {α} {A : Set α} -> (A -> Kind) -> Con A -> Kind -> Kind
conToKindBy f Θ τ = foldrᶜ (_⇒ᵏ_ ∘ f) τ Θ

-- | Right-fold a context with `_⇒ᵏ_`.
--
-- > conToKind (ε ▻ σ₁ ▻ … ▻ σₙ) τ = σ₁ ⇒ᵏ … ⇒ᵏ σₙ ⇒ᵏ τ
conToKind : Conᵏ -> Kind -> Kind
conToKind = conToKindBy id

-- | Construct an environment with n variables going in reverse order.
--
-- > subVars' = ∅ ▷ (n - 1) ▷ … ▷ 0
--
-- (each variable is denoted by its De Bruijn index).
subVars' : ∀ {Θ Ξ} -> Seq (λ σ -> Ξ ▻▻ Θ ⊢ᵗ σ) Θ
subVars' {ε}     = ø
subVars' {Θ ▻ σ} = mapˢ shiftᵗ subVars' ▶ Var vz

-- | Construct an environment with n variables going in reverse order.
--
-- > subVars' = ∅ ▷ (n - 1) ▷ … ▷ 0
--
-- (each variable is denoted by its De Bruijn index).
subVars : ∀ {α} {A : Set α} {Ξ Θ} {f : A -> Kind} -> Seq (λ σ -> Ξ ▻▻ mapᶜ f Θ ⊢ᵗ f σ) Θ
subVars {Θ = ε}     = ø
subVars {Θ = Θ ▻ σ} = mapˢ shiftᵗ subVars ▶ Var vz

-- | Apply π` to a type `n` times.
--
-- > πⁿ' (ε ▻ σ₁ ▻ … ▻ σₙ) β = πₙ ∘ … ∘ π₁ $ β
πⁿ' : ∀ {Ξ} Θ -> Star (Ξ ▻▻ Θ) -> Star Ξ
πⁿ'  ε      β = β
πⁿ' (Θ ▻ σ) β = πⁿ' Θ (π σ β)

-- | Apply `Lam` to a type `n` times.
--
-- > Lamⁿ' (ε ▻ σ₁ ▻ … ▻ σₙ) β = Lamₙ ∘ … ∘ Lam₁ $ β
Lamⁿ' : ∀ {Ξ τ} Θ -> Ξ ▻▻ Θ ⊢ᵗ τ -> Ξ ⊢ᵗ conToKind Θ τ
Lamⁿ'  ε      β = β
Lamⁿ' (Θ ▻ σ) β = Lamⁿ' Θ (Lam β)

-- | Apply `Lam` to a type `n` times.
--
-- > Lamⁿ' (ε ▻ σ₁ ▻ … ▻ σₙ) β = Lamₙ ∘ … ∘ Lam₁ $ β
Lamⁿ : ∀ {α} {A : Set α} {Ξ τ f} (Θ : Con A) -> Ξ ▻▻ mapᶜ f Θ ⊢ᵗ τ -> Ξ ⊢ᵗ conToKindBy f Θ τ
Lamⁿ  ε      β = β
Lamⁿ (Θ ▻ σ) β = Lamⁿ Θ (Lam β)

-- | Apply a type function to an environment.
--
-- > applyᵗⁿ _ ψ (∅ ▷ α₁ ▷ … ▷ αₙ) = ψ α₁ … αₙ
applyᵗⁿ
  : ∀ {α} {A : Set α} {Ξ f τ}
  -> (Θ : Con A)
  -> Ξ ⊢ᵗ foldrᶜ (_⇒ᵏ_ ∘ f) τ Θ
  -> Seq (λ σ -> Ξ ⊢ᵗ f σ) Θ
  -> Ξ ⊢ᵗ τ
applyᵗⁿ _ ψ  ø      = ψ
applyᵗⁿ _ ψ (ρ ▶ α) = applyᵗⁿ _ ψ ρ ∙ α

instᵗⁿ
  : ∀ {α} {A : Set α} {Θ Ξ σ} {f : Con A -> Kind}
  -> Seq (λ τ -> Θ ⊢ᵗ f τ) Ξ -> Θ ▻▻ mapᶜ f Ξ ⊢ᵗ σ -> Θ ⊢ᵗ σ
instᵗⁿ              ø      β = β
instᵗⁿ {Ξ = Ξ ▻ _} (ρ ▶ α) β = instᵗⁿ ρ (bindᵗ (shiftᵗⁿ (mapᶜ _ Ξ) α) β)

instᵗⁿ' : ∀ {Θ Ξ σ} -> Seq (Θ ⊢ᵗ_) Ξ -> Θ ▻▻ Ξ ⊢ᵗ σ -> Θ ⊢ᵗ σ
instᵗⁿ'              ø      β = β
instᵗⁿ' {Ξ = Ξ ▻ _} (ρ ▶ α) β = instᵗⁿ' ρ (bindᵗ (shiftᵗⁿ Ξ α) β)

conToTypeBy : ∀ {Θ Ξ} -> (Star Θ -> Star Ξ) -> Con (Star Θ) -> Star Ξ -> Star Ξ
conToTypeBy f Δ β = foldrᶜ (_⇒_ ∘ f) β Δ
