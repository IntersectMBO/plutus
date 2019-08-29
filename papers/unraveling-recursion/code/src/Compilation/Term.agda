module Compilation.Term where

open import Context
open import Type.Core
open import Type.NbE
import Term.Core as Core
open import Compilation.Data
open import Compilation.Encode.Core

open import Function
open import Data.Empty
open import Data.Sum.Base
open import Data.List.Base as List

infix 3 _⊢_

data Recursivity : Set where
  NonRec Rec : Recursivity

caseRec : ∀ {ρ} {R : Set ρ} -> Recursivity -> R -> R -> R
caseRec NonRec x y = x
caseRec Rec    x y = y

data _⊢_ {Θ} Γ : Star Θ -> Set where
  letType : ∀ {σ β} -> (α : Θ ⊢ᵗ σ) -> shiftᶜ Γ ⊢ β -> Γ ⊢ β [ α ]ᵗ
  letTerm : ∀ {α} Δ rec -> Seq (caseRec rec Γ (Γ ▻▻ Δ) ⊢_) Δ -> Γ ▻▻ Δ ⊢ α -> Γ ⊢ α
  var  : ∀ {α}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {σ α} -> shiftᶜ Γ ⊢ α -> Γ ⊢ π σ α
  _[_] : ∀ {σ β} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  ƛ_   : ∀ {α β} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {α β} -> Γ ⊢ α ⇒ β -> Γ ⊢ α -> Γ ⊢ β
  iwrap  : ∀ {κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ Core.unfold ψ α -> Γ ⊢ μ ψ α
  unwrap : ∀ {κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ μ ψ α -> Γ ⊢ Core.unfold ψ α

mutual
  compile : ∀ {Θ} {Γ : Con (Star Θ)} {α} -> Γ ⊢ α -> Γ Core.⊢ α
  compile (letType α term)         = (Core.Λ (compile term)) Core.[ α ]
  compile (letTerm Δ rec env term) with rec
  ... | NonRec = Core.instNonRec (map-compile env) (compile term)
  ... | Rec    = Core.instRec    (map-compile env) (compile term)
  compile (var v)                  = Core.var v
  compile (Λ body)                 = Core.Λ (compile body)
  compile (fun [ α ])              = compile fun Core.[ α ]
  compile (ƛ body)                 = Core.ƛ (compile body)
  compile (fun · arg)              = compile fun Core.· compile arg
  compile (iwrap  term)            = Core.iwrap (compile term)
  compile (unwrap term)            = Core.unwrap (compile term)

  -- This is just `mapˢ compile` inlined to convince Agda there are no termination problems.
  map-compile : ∀ {Θ} {Γ Δ : Con (Star Θ)} -> Seq (Γ ⊢_) Δ -> Seq (Γ Core.⊢_) Δ
  map-compile  ø           = ø
  map-compile (seq ▶ term) = map-compile seq ▶ compile term
