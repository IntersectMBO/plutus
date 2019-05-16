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
open import Scoped
open import Scoped.Extrication
open import Algorithmic.RenamingSubstitution as AS
open import Scoped.RenamingSubstitution as SS
open import Builtin

-- type renamings

extricateRenNf⋆ : ∀{Γ Δ}(ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) 
  → Ren⋆ (len⋆ Γ) (len⋆ Δ)
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ zero = extricateVar⋆ (ρ⋆ Z)
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ (suc α) = extricateRenNf⋆ (ρ⋆ ∘ S) α

ren-extricateVar⋆ : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → extricateRenNf⋆ ρ⋆ (extricateVar⋆ α) ≡ extricateVar⋆ (ρ⋆ α)
ren-extricateVar⋆ ρ⋆ Z     = refl
ren-extricateVar⋆ ρ⋆ (S α) = ren-extricateVar⋆ (ρ⋆ ∘ S) α

{-
lift⋆-extricate⋆ : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Fin (suc (len⋆ Γ)))
  → lift⋆ (extricateRenNf⋆ ρ⋆) A ≡ extricateRenNf⋆ {Γ ,⋆ K} {Δ ,⋆ K} (T.ext ρ⋆) A
lift⋆-extricate⋆ ρ⋆ zero = refl
lift⋆-extricate⋆ ρ⋆ (suc α) = {!!}

ren⋆-extricate⋆ : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢Nf⋆ K)
  → ren⋆ (extricateRenNf⋆ ρ⋆) (extricateNf⋆ A) ≡ extricateNf⋆ (renameNf ρ⋆ A)
ren⋆-extricate⋆ ρ⋆ (Π A) = cong
  (Π "x" (extricateK _))
  (trans
    {!ren⋆-extricate ρ⋆!} -- (ren⋆-cong {!!} (extricateNf⋆ A))
    (ren⋆-extricate⋆ (T.ext ρ⋆) A))
ren⋆-extricate⋆ ρ⋆ (A ⇒ B) = cong₂ _⇒_ (ren⋆-extricate⋆ ρ⋆ A) (ren⋆-extricate⋆ ρ⋆ B)
ren⋆-extricate⋆ ρ⋆ (ƛ A) = cong
  (ƛ "x" (extricateK _))
  (trans
    {!!}
    (ren⋆-extricate⋆ (T.ext ρ⋆) A))
ren⋆-extricate⋆ ρ⋆ (ne x) = {!!}
ren⋆-extricate⋆ ρ⋆ (con x) = refl
-}
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

{-
ren-extricateVar-T : ∀{Δ K}{A A' : A.∥ Δ ∥ ⊢Nf⋆ K}(p :  A ≡ A') → (x : Δ ∋ A) → 
  extricateVar (Eq.subst (Δ ∋_) p x)
  ≡
  extricateVar x
ren-extricateVar-T refl x = refl

ren-extricateVar : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (ρ : ∀ {J} {A : A.∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → {A : A.∥ Γ ∥ ⊢Nf⋆ J}
  → (x : Γ ∋ A)
  → extricateRen ρ⋆ ρ (extricateVar x) ≡ extricateVar (ρ x)
ren-extricateVar ρ⋆ ρ Z = refl
ren-extricateVar ρ⋆ ρ (S x) = ren-extricateVar ρ⋆ (ρ ∘ S) x 
ren-extricateVar {Γ ,⋆ K}{Δ} ρ⋆ ρ (T {A = A} x) = trans
  (ren-extricateVar
    (ρ⋆ ∘ S)
    (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renameNf-comp A)) (ρ (T x)))
    x)
  (ren-extricateVar-T (sym (renameNf-comp A)) (ρ (T x)))

extricateRenNf⋆-comp : ∀{B Γ Δ}(ρ⋆' : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)(ρ⋆ : ∀ {J} → B ∋⋆ J → Γ ∋⋆ J) → ∀ x → (extricateRenNf⋆ ρ⋆' ∘ extricateRenNf⋆ ρ⋆) x ≡ extricateRenNf⋆ (ρ⋆' ∘ ρ⋆) x
extricateRenNf⋆-comp {B ,⋆ K} ρ⋆' ρ⋆ zero = ren-extricateVar⋆ ρ⋆' (ρ⋆ Z)
extricateRenNf⋆-comp {B ,⋆ K} ρ⋆' ρ⋆ (suc x) = extricateRenNf⋆-comp ρ⋆' (ρ⋆ ∘ S) x  

-- I guess i could prove identity as well

-- here it starts to go south

ren-extricateƛ₁ : ∀{Γ Δ Γ' Δ' K}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (A  : A.∥ Γ ∥ ⊢Nf⋆ K)
  → (p : len⋆ A.∥ Γ ∥ ≡ Γ')
  → (q : len⋆ A.∥ Δ ∥ ≡ Δ')
  → ren⋆ (subst₂ Ren⋆ p q (extricateRenNf⋆ ρ⋆))
    (Eq.subst ScopedTy p (extricateNf⋆ A)) 
    ≡ Eq.subst ScopedTy q (extricateNf⋆ (renameNf ρ⋆ A))
ren-extricateƛ₁ ρ⋆ A refl refl = {!!}

ren-extricate : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (ρ : ∀ {J} {A : A.∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → {A : A.∥ Γ ∥ ⊢Nf⋆ J}
  → (t : Γ ⊢ A)
  →  SS.ren
       (subst₂ Ren⋆ (sym (lem Γ)) (sym (lem Δ)) (extricateRenNf⋆ ρ⋆))
       (extricateRen ρ⋆ ρ)
       (extricate t)
     ≡ extricate (AS.rename ρ⋆ ρ t)


ren-extricate ρ⋆ ρ (` x) = cong ` (ren-extricateVar ρ⋆ ρ x)
ren-extricate ρ⋆ ρ (ƛ t) = cong₂ (ƛ "x") {!ren!} {!!} 
ren-extricate ρ⋆ ρ (t · u) = cong₂ _·_ (ren-extricate ρ⋆ ρ t) (ren-extricate ρ⋆ ρ u)
ren-extricate ρ⋆ ρ (Λ t) = cong (Λ "x" (extricateK _)) {!ren-extricate (T.ext ρ⋆) (AS.ext⋆ ρ⋆ ρ) t!}
ren-extricate ρ⋆ ρ (t ·⋆ A) = {!!}
ren-extricate ρ⋆ ρ (wrap1 pat arg t) = {!!}
ren-extricate ρ⋆ ρ (unwrap1 t) = {!!}
ren-extricate ρ⋆ ρ (con x) = {!!}
ren-extricate ρ⋆ ρ (builtin bn σ ts) = {!cong (builtin bn)!}
ren-extricate {Γ}{Δ} ρ⋆ ρ (error A) = cong error {!!}

-- I need to use the same kind of techniques as the
-- soundness/completeness proofs for Declarative/Algorithmic
-}
\end{code}

\begin{code}
-- a naturality/simulation proof about intrinscially vs extrinsically typed evaluation connected by erasure

open import Data.Sum
open import Algorithmic.Reduction as AR
open import Algorithmic.Evaluation as AE
open import Scoped.Reduction as SR
open import Utils

extricate—→ : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}{t t' : Γ ⊢ A} → t AR.—→ t' → extricate t SR.—→ extricate t'
extricateVal : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}{t : Γ ⊢ A} → AR.Value t → SR.Value (extricate t)
extricateE : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{t : Γ ⊢ A} → AR.Error t → SR.Error (extricate t)
extricateE E-error = E-error _
extricateE (E-·₁ p) = E-·₁ (extricateE p)
extricateE (E-·₂ p) = E-·₂ (extricateE p)
extricateE (E-·⋆ p) = E-·⋆ (extricateE p)
extricateE (E-unwrap p) = E-unwrap (extricateE p)
extricateE (E-builtin bn σ tel Bs Ds vtel x p tel') = E-builtin (extricateE x)

extricateVal V-ƛ = V-ƛ "x" _ _
extricateVal V-Λ_ = SR.V-Λ "x" _ _
extricateVal V-wrap1 = V-wrap _ _ _
extricateVal (V-con cn) = V-con (extricateC cn)

extricate—→ (ξ-·₁ p)   = ξ-·₁ (extricate—→ p)
extricate—→ (ξ-·₂ p q) = ξ-·₂ (extricateVal p) (extricate—→ q)
extricate—→ (ξ-·⋆ p) = ξ-·⋆ (extricate—→ p)
extricate—→ (β-ƛ {A = A}{N = N}{W = W} p) = Eq.subst
  (ƛ "x" (extricateNf⋆ A) (extricate N) · extricate W  SR.—→_)
  {!!}
  SR.β-ƛ
extricate—→ (β-Λ {K = K}{N = N}{W = W}) = Eq.subst
  (Λ "x" (extricateK K) (extricate N) ·⋆ extricateNf⋆ W SR.—→_)
  {!!}
  SR.β-Λ
extricate—→ β-wrap1 = β-wrap
extricate—→ (ξ-unwrap1 p) = ξ-unwrap (extricate—→ p)
extricate—→ (β-builtin bn σ tel vtel) = {!!}
extricate—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!SR.ξ-builtin {b = bn} ? (extricate—→ p) ?!}

{-
theorem : {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) → 
  -- for any n such that eval terminates with a value, then run also terminates with the erasure of the same value
  ∀ n → (p : Σ (∅ ⊢ A) λ t' → Σ (t AR.—↠ t') λ p → Σ (AR.Value t') λ v → eval (gas n) t ≡ steps p (done t' v))
  → proj₁ (run (extricate t) n) ≡ extricate (proj₁ p) × Σ (SR.Value (proj₁ (run (extricate t) n))) λ v → proj₂ (proj₂ (run (extricate t) n)) ≡ inj₁ (just v)
  -- question: is the last clause needed?
theorem t (suc n) (t' P., p P., v P., q) with AR.progress t | SR.progress (extricate t)
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₁ q' = {!!}
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₂ y = {!!}
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₁ v'') = refl P., (v'' P., refl)
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₂ e) = refl P., {!!} -- missing info, I would need that something reduces to e...
theorem t (suc n) (t' P., p P., v P., q) | done x | inj₂ y = {!!}
-}
\end{code}
