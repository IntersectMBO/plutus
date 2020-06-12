# CEK machine that discharges builtin args

```
module Algorithmic.CEKV where

open import Function hiding (_∋_)
open import Data.Product using (proj₁;proj₂)
import Data.List as L
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.Sum

open import Type
open import Type.BetaNormal
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con

data Env : Ctx ∅ → Set

data Value : (A : ∅ ⊢Nf⋆ *) → Set where
  V-ƛ : ∀ {Γ}{A B : ∅ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
    → Env Γ
    → Value (A ⇒ B)

  V-Λ : ∀ {Γ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
    → Env Γ
    → Value (Π B)

  V-wrap : ∀{K}
   → {pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∅ ⊢Nf⋆ K}
   → Value (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
   → Value (ne (μ1 · pat · arg))

  V-con : {tcn : TyCon}
    → (cn : TermCon {∅} (con tcn))
    → Value (con tcn)

data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ

VTel : ∀ Δ → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)(As : L.List (Δ ⊢Nf⋆ *)) → Set
VTel Δ σ L.[]       = ⊤
VTel Δ σ (A L.∷ As) = Value (substNf σ A) × VTel Δ σ As

extendVTel : ∀{Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vs : VTel Δ σ Bs)
    → ∀{C}(v : Value (substNf σ C))
    → (p : Bs L.++ (C L.∷ L.[]) ≡ As)
    → VTel Δ σ As
extendVTel L.[] σ vs v refl = v ,, _
extendVTel (B L.∷ Bs) σ (v ,, vs) v' refl = v ,, extendVTel Bs σ vs v' refl


BUILTIN : (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vtel : VTel Δ σ As)
      -----------------------------
    → Value (substNf σ C) ⊎ ∅ ⊢Nf⋆ *
BUILTIN b σ vtel = inj₂ (substNf σ (proj₂ (proj₂ (SIG b))))

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Value (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (ne (μ1 · pat · arg))
            (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
            (ne (μ1 · pat · arg))
            
  builtin- : ∀{Γ}(b : Builtin)
    → (σ : ∀ {K} → proj₁ (SIG b) ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (As : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (vs : VTel (proj₁ (SIG b)) σ As)
    → (A : (proj₁ (SIG b) ⊢Nf⋆ *))
    → (As' : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → proj₁ (proj₂ (SIG b)) ≡ As L.++ A L.∷ As'
    → Tel Γ (proj₁ (SIG b)) σ As'
    → Env Γ
    → Frame (substNf σ (proj₂ (proj₂ (SIG b)))) (substNf σ A)

data Stack (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  ε   : Stack T T
  _,_ : ∀{H1 H2} → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → Value H → State T
  □     : Value T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)             = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)             = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))         = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)             = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A))        = (s , -·⋆ A) ; ρ ▻ L 
step (s ; ρ ▻ wrap1 pat arg L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap1 {pat = pat}{arg} L) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c) = s ◅ V-con c
step (s ; ρ ▻ builtin bn σ ts) with proj₁ (proj₂ (SIG bn)) | inspect (proj₁ ∘ proj₂ ∘ SIG) bn
step (s ; ρ ▻ builtin bn σ [])       | L.[]     | [[ p ]]
  with BUILTIN bn σ (substEq (VTel (proj₁ (SIG bn)) σ ) (sym p) _)
... | inj₁ V = s ◅ V
... | inj₂ A = ◆ A
step (s ; ρ ▻ builtin bn σ (t ∷ ts)) | A L.∷ As | [[ p ]] =
  (s , builtin- bn σ L.[] _ A As p ts ρ) ; ρ ▻ t
step (s ; ρ ▻ error A) = ◆ A
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {pat = pat}{arg = arg}) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step ((s , builtin- b σ As vs A L.[] p ts' ρ) ◅ V)
  with BUILTIN b σ (extendVTel As σ vs V (sym p))
... | inj₁ V' = s ◅ V'
... | inj₂ A' = ◆ A'
step ((s , builtin- b σ As vs A (A' L.∷ As') p (t' ∷ ts') ρ) ◅ V) =
  (s , builtin-
         b
         σ
         (As L.++ L.[ A ])
         (extendVTel As σ vs V refl)
         A'
         As'
         (trans p (sym (++-assoc As L.[ A ] (A' L.∷ As'))))
         ts'
         ρ)
   ; ρ ▻ t'
step (□ V) = □ V
step (◆ A) = ◆ A
