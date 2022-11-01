{-# OPTIONS --rewriting #-}

module Term.Core where

open import Context
open import Type

open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Unit.Base
open import Data.Sum.Base

{-# BUILTIN REWRITE _≡_ #-}

{-# REWRITE foldlᶜ-▻-ε #-}
{-# REWRITE mapᶜ-▻▻    #-}

{-# REWRITE keep-id      #-}
{-# REWRITE dupl-keep-vs #-}

{-# REWRITE renᵗ-id #-}
{-# REWRITE renᵗ-∘  #-}

{-# REWRITE subᵗ-idᵉ  #-}
{-# REWRITE subᵗ-renᵗ #-}
{-# REWRITE subᵗ-Var  #-}

{-# REWRITE inject-foldr-⇒-renᵗ #-}
{-# REWRITE inject-foldr-⇒-subᵗ #-}

infix  3 _⊢_
infix  4 Λ_ ƛ_
infixl 7 _·_
infix  9 _[_]

unfold : ∀ {Θ κ} -> Θ ⊢ᵗ (κ ⇒ᵏ ⋆) ⇒ᵏ κ ⇒ᵏ ⋆ -> Θ ⊢ᵗ κ -> Θ ⊢ᵗ ⋆
unfold ψ α = normalize $ ψ ∙ Lam (μ (shiftᵗ ψ) (Var vz)) ∙ α

data _⊢_ : ∀ {Θ} -> Con (Star Θ) -> Star Θ -> Set where
  var  : ∀ {Θ Γ} {α : Star Θ}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {Θ Γ σ} {α : Star (Θ ▻ σ)} -> shiftᶜ Γ ⊢ α -> Γ ⊢ π σ α
  -- A normalizing at the type level type instantiation.
  _[_] : ∀ {Θ Γ σ} {β : Star (Θ ▻ σ)} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  -- A non-normalizing at the type level type instantiation.
  _<_> : ∀ {Θ Γ σ} {β : Star (Θ ▻ σ)} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β < α >ᵗ
  -- A shorthand for `_< Var vz >` with more convenient computation at the type level.
  _<>  : ∀ {Θ σ Γ} {β : Star (Θ ▻ σ ▻ σ)} -> Γ ⊢ π σ β -> Γ ⊢ unshiftᵗ β
  ƛ_   : ∀ {Θ Γ} {α β : Star Θ} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {Θ Γ} {α β : Star Θ} -> Γ ⊢ α ⇒ β -> Γ ⊢ α -> Γ ⊢ β
  iwrap  : ∀ {Θ Γ κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ unfold ψ α -> Γ ⊢ μ ψ α
  unwrap : ∀ {Θ Γ κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ μ ψ α -> Γ ⊢ unfold ψ α

Term⁺ : Star⁺ -> Set
Term⁺ α = ∀ {Θ} {Γ : Con (Star Θ)} -> Γ ⊢ normalize α

Term⁻ : ∀ {Θ} -> Star Θ -> Set
Term⁻ α = ∀ {Γ} -> Γ ⊢ normalize α

bind : ∀ {Θ Γ} {α β : Star Θ} -> Γ ⊢ α -> Γ ▻ α ⊢ β -> Γ ⊢ β
bind term body = (ƛ body) · term

ren : ∀ {Θ Γ Δ} {α : Star Θ} -> Γ ⊆ Δ -> Γ ⊢ α -> Δ ⊢ α
ren ι (var v)       = var (renᵛ ι v)
ren ι (Λ body)      = Λ (ren (mapᶜ-⊆ ι) body)
ren ι (fun [ α ])   = ren ι fun [ α ]
ren ι (fun < α >)   = ren ι fun < α >
ren ι (fun <>)      = ren ι fun <>
ren ι (ƛ body)      = ƛ (ren (keep ι) body)
ren ι (fun · arg)   = ren ι fun · ren ι arg
ren ι (iwrap  term) = iwrap (ren ι term)
ren ι (unwrap term) = unwrap (ren ι term)

shiftⁿ : ∀ {Θ Γ} {α : Star Θ} Δ -> Γ ⊢ α -> Γ ▻▻ Δ ⊢ α
shiftⁿ = ren ∘ extʳ

shift : ∀ {Θ Γ} {α β : Star Θ} -> Γ ⊢ α -> Γ ▻ β ⊢ α
shift = shiftⁿ (ε ▻ _)

instNonRec : ∀ {Θ Γ Δ} {α : Star Θ} -> Seq (Γ ⊢_) Δ -> Γ ▻▻ Δ ⊢ α -> Γ ⊢ α
instNonRec              ø           body = body
instNonRec {Δ = Δ ▻ _} (seq ▶ term) body = instNonRec seq (bind (shiftⁿ Δ term) body)

module Y where
  self : Type⁺ (⋆ ⇒ᵏ ⋆)
  self = Lam μ (Lam Lam (Var (vs vz) ∙ Var vz ⇒ Var vz)) (Var vz)

  unfoldˢ : Term⁺ (π ⋆ $ self ∙ Var vz ⇒ self ∙ Var vz ⇒ Var vz)
  unfoldˢ = Λ ƛ unwrap (var vz)

  unrollˢ : Term⁺ (π ⋆ $ self ∙ Var vz ⇒ Var vz)
  unrollˢ = Λ ƛ unfoldˢ [ Var vz ] · var vz · var vz

  fix : Term⁺ (π ⋆ $ (Var vz ⇒ Var vz) ⇒ Var vz)
  fix = Λ ƛ unrollˢ [ Var vz ] · iwrap (ƛ var (vs vz) · (unrollˢ [ Var vz ] · var vz))
open Y using (fix)

tuple : ∀ {Θ} -> Star (Θ ▻ ⋆) -> Star Θ
tuple Fv = π ⋆ $ Fv ⇒ Var vz

endo : ∀ {Θ} -> Star (Θ ▻ ⋆) -> Star Θ
endo Fv = π ⋆ $ Fv ⇒ Fv

fixBy
  : ∀ {Θ} {Γ : Con (Star Θ)}
  -> (Fv : Star (Θ ▻ ⋆))
  -> Γ ⊢ (tuple Fv ⇒ tuple Fv) ⇒ endo Fv ⇒ tuple Fv
fixBy Fv =
  ƛ fix < endo Fv ⇒ tuple Fv > ·
    (ƛ ƛ Λ ƛ (var (vs vs vs vz) ·
      (Λ ƛ (var (vs vs vs vz) · var (vs vs vz)) <> ·
        -- `bind` is in order to make REWRITE rules fire (yeah, it's silly).
        (bind (var (vs vs vz) <>) (var vz) · var vz))) <> · var vz)

ƛⁿ
  : ∀ {Θ Ξ Γ} {f : Star Ξ -> Star Θ} {β}
  -> ∀ Δ -> Γ ▻▻ mapᶜ f Δ ⊢ β -> Γ ⊢ conToTypeBy f Δ β
ƛⁿ  ε      term = term
ƛⁿ (Δ ▻ τ) body = ƛⁿ Δ (ƛ body)

ƛⁿ'
  : ∀ {Θ Γ} {β : Star Θ}
  -> ∀ Δ -> Γ ▻▻ Δ ⊢ β -> Γ ⊢ conToTypeBy id Δ β
ƛⁿ'  ε      term = term
ƛⁿ' (Δ ▻ τ) body = ƛⁿ' Δ (ƛ body)

applyⁿ
  : ∀ {Θ Ξ Γ} {β : Star Θ} {f : Star Ξ -> Star Θ}
  -> ∀ Δ -> Γ ⊢ conToTypeBy f Δ β -> Seq (λ τ -> Γ ⊢ f τ) Δ -> Γ ⊢ β
applyⁿ _ y  ø        = y
applyⁿ _ f (seq ▶ x) = applyⁿ _ f seq · x

deeply
  : ∀ {Θ Ξ Γ} {f : Star Ξ -> Star Θ} {β γ}
  -> ∀ Δ
  -> Γ ▻▻ mapᶜ f Δ ⊢ β ⇒ γ
  -> Γ ⊢ conToTypeBy f Δ β
  -> Γ ⊢ conToTypeBy f Δ γ
deeply  ε      g y = g · y
deeply (Δ ▻ τ) g f = deeply Δ (ƛ ƛ shiftⁿ (ε ▻ _ ▻ _) (ƛ g) · var vz · (var (vs vz) · var vz)) f

conToTypeShift : ∀ {Θ} -> Con (Star Θ) -> Star (Θ ▻ ⋆)
conToTypeShift Δ = conToTypeBy shiftᵗ Δ (Var vz)

-- This is not easy, but makes perfect sense and should be doable.
postulate
  shift-⊢ : ∀ {Θ Γ β} {α : Star Θ} -> Γ ⊢ α -> shiftᶜ {τ = β} Γ ⊢ shiftᵗ α

recursive
  : ∀ {Θ} {Γ : Con (Star (Θ ▻ ⋆))}
  -> (Δ : Con (Star Θ))
  -> Γ ⊢ π ⋆ (conToTypeBy (shiftᵗⁿ (ε ▻ _ ▻ _)) Δ (Var vz) ⇒ Var vz)
  -> Seq (λ β -> Γ ⊢ shiftᵗ β) Δ
recursive  ε      h = ø
recursive (Δ ▻ τ) h
  = recursive Δ (Λ ƛ shift (shift-⊢ h <>) · deeply Δ (ƛ ƛ var (vs vz)) (var vz))
  ▶ h < shiftᵗ τ > · (ƛⁿ Δ (ƛ var vz)) where

byCon : ∀ {Θ} (Δ : Con (Star Θ)) -> let F = conToTypeShift Δ in ∀ {Γ} -> Γ ⊢ tuple F ⇒ tuple F
byCon Δ = ƛ Λ ƛ applyⁿ Δ (var vz) (recursive Δ (var (vs vz)))

fixCon : ∀ {Θ} (Δ : Con (Star Θ)) -> let F = conToTypeShift Δ in ∀ {Γ} -> Γ ⊢ endo F ⇒ tuple F
fixCon Δ = fixBy (conToTypeShift Δ) · byCon Δ

record Tuple {Θ} (Γ Δ : Con (Star Θ)) : Set where
  constructor PackTuple
  field tupleTerm : Γ ⊢ tuple (conToTypeShift Δ)

mutualFix : ∀ {Θ} {Γ Δ : Con (Star Θ)} -> Seq (Γ ▻▻ Δ ⊢_) Δ -> Tuple Γ Δ
mutualFix {Γ = Γ} {Δ} seq
  = PackTuple
  $ fixCon Δ
  · (Λ ƛ ƛⁿ Δ (applyⁿ Δ (var (vsⁿ (shiftᶜ Δ))) $
      mapˢ (ren (keepⁿ (shiftᶜ Δ) ∘ extʳ $ ε ▻ _) ∘′ shift-⊢) seq))

-- Note that we do not perform the "pass the whole tuple in and extract each its element
-- separately" trick, because we do know the type of the result (it's `α`).
bindTuple : ∀ {Θ Γ Δ} {α : Star Θ} -> Tuple Γ Δ -> Γ ▻▻ Δ ⊢ α -> Γ ⊢ α
bindTuple {Θ} {Γ} {Δ} {α} (PackTuple tup) body = tup < α > · (ƛⁿ Δ body)

instRec : ∀ {Θ Γ Δ} {α : Star Θ} -> Seq (Γ ▻▻ Δ ⊢_) Δ -> Γ ▻▻ Δ ⊢ α -> Γ ⊢ α
instRec = bindTuple ∘ mutualFix
