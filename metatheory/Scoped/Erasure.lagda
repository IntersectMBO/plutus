\begin{code}
module Scoped.Erasure where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic as A
open import Scoped
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
open import Data.Nat
open import Data.Fin
\end{code}

\begin{code}
len : Ctx → Weirdℕ
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

len⋆ : Ctx⋆ → ℕ
len⋆ ∅ = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

-- scoped kind clearly shoud go...
eraseK : Kind → ScopedKind
eraseK * = *
eraseK # = #
eraseK (K ⇒ J) = eraseK K ⇒ eraseK J

eraseVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
eraseVar⋆ Z     = zero
eraseVar⋆ (S α) = suc (eraseVar⋆ α)

eraseNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
eraseNe⋆ : ∀{Γ K}(A : Γ ⊢NeN⋆ K) → ScopedTy (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

eraseNf⋆ (Π {K = K} A) = Π "x" (eraseK K) (eraseNf⋆ A)
eraseNf⋆ (A ⇒ B) = eraseNf⋆ A ⇒ eraseNf⋆ B
eraseNf⋆ (ƛ {K = K} A) = ƛ "x" (eraseK K) (eraseNf⋆ A)
eraseNf⋆ (ne n) = eraseNe⋆ n
eraseNf⋆ (size⋆ n) = size n
eraseNf⋆ (con c A) = con c

eraseNe⋆ (` α) = ` (eraseVar⋆ α)
eraseNe⋆ (n · n') = eraseNe⋆ n · eraseNf⋆ n'
-- ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *
eraseNe⋆ (μ1 {K = K}) = ƛ "x"
  ((eraseK K ⇒ *) ⇒ eraseK K ⇒ *)
  (ƛ "y" (eraseK K) (μ (` (suc zero)) (` zero)))

eraseVar : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K} → Γ ∋ A → WeirdFin (len Γ)
eraseVar Z = Z
eraseVar (S x) = S (eraseVar x)
eraseVar (T x) = T (eraseVar x)

open import Relation.Binary.PropositionalEquality
lem : ∀ Γ → Scoped.∥ len Γ ∥ ≡ len⋆ A.∥ Γ ∥
lem ∅ = refl
lem (Γ ,⋆ K) = cong suc (lem Γ)
lem (Γ , A) = lem Γ

eraseNf⋆' : ∀ Γ {K}(A : A.∥ Γ ∥ ⊢Nf⋆ K) → ScopedTy Scoped.∥ len Γ ∥
eraseNf⋆' Γ A rewrite lem Γ = eraseNf⋆ A


eraseC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → TermCon A → SizedTermCon
eraseC (integer s i p) = integer s i p
eraseC (bytestring s b p) = bytestring s b p
eraseC (size s) = size s

open import Data.List as L
open import Data.Product as P
open import Function

eraseSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J) → List (ScopedTy (len⋆ Γ))
eraseSub {Δ = ∅} σ = []
eraseSub {Δ = Δ ,⋆ K} σ = eraseSub {Δ = Δ} (σ ∘ S) ++ L.[ eraseNf⋆ (σ Z) ]

eraseSub' : ∀ Γ {Δ} → (∀ {J} → Δ ∋⋆ J → A.∥ Γ ∥ ⊢Nf⋆ J)
  → List (ScopedTy (Scoped.∥ len Γ ∥))
eraseSub' Γ rewrite lem Γ = eraseSub

eraseTel : ∀ {Γ Δ}(σ : ∀ {J} → Δ ∋⋆ J → A.∥ Γ ∥ ⊢Nf⋆ J)(as : List (Δ ⊢Nf⋆ *)) → Tel Γ Δ σ as
  → List (ScopedTm (len Γ))
erase : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K} → Γ ⊢ A → ScopedTm (len Γ)

eraseTel σ [] x = []
eraseTel σ (A ∷ As) (t P., ts) = eraseTel σ As ts ++ L.[ erase t ]

erase (` x) = ` (eraseVar x)
erase {Γ} (ƛ {A = A} t) = ƛ "x" (eraseNf⋆' Γ A) (erase t)
erase (t · u) = erase t · erase u
erase (Λ {K = K} t) = Λ "x" (eraseK K) (erase t)
erase {Γ} (t ·⋆ A) = erase t ·⋆ eraseNf⋆' Γ A
erase {Γ} (wrap1 pat arg t) = wrap (eraseNf⋆' Γ pat) (eraseNf⋆' Γ arg) (erase t)
erase (unwrap1 t) = unwrap (erase t)
erase (con c) = con (eraseC c)
erase {Γ} (builtin b σ ts) = builtin b (eraseSub' Γ σ) (eraseTel σ _ ts)
erase {Γ} (error A) = error (eraseNf⋆' Γ A)
\end{code}

\begin{code}
-- a naturality/simulation proof about intrinscially vs extrinsically typed evaluation connected by erasure

open import Data.Sum
open import Algorithmic.Reduction as AR
open import Algorithmic.Evaluation as AE
open import Scoped.Reduction as SR
open import Utils
{-
erase—→ : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K}{t t' : Γ ⊢ A} → t AR.—→ t' → erase t SR.—→ erase t'
eraseVal : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K}{t : Γ ⊢ A} → AR.Value t → SR.Value (erase t)
eraseVal V-ƛ = V-ƛ "x" _ _
eraseVal V-Λ_ = SR.V-Λ "x" _ _
eraseVal V-wrap1 = V-wrap _ _ _
eraseVal (V-con cn) = V-con (eraseC cn)

erase—→ (ξ-·₁ p)   = ξ-·₁ (erase—→ p)
erase—→ (ξ-·₂ p q) = ξ-·₂ (eraseVal p) (erase—→ q)
erase—→ (E-·₁ p) = {!E-!}
erase—→ (E-·₂ p) = {!!}
erase—→ (ξ-·⋆ p) = ξ-·⋆ (erase—→ p)
erase—→ (E-·⋆ p) = {!!}
erase—→ (β-ƛ p) = {!SR.β-ƛ!}
erase—→ β-Λ = {!!}
erase—→ β-wrap1 = β-wrap
erase—→ (ξ-unwrap1 p) = {!!}
erase—→ (E-unwrap1 p₁) = {!!}
erase—→ (β-builtin bn σ tel vtel) = {!!}
erase—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!!}
erase—→ (E-builtin bn σ tel Bs Ds vtel p p' tel') = {!!}


lemma : {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) →
  (Σ (∅ ⊢ A) λ t' → Σ (t AR.—→ t') λ p → AR.progress t ≡ step p
    × SR.progress (erase t) ≡ inj₂ (erase t' P., {!!}))
  ⊎
  (Σ (AR.Value t) λ v → AR.progress t ≡ done v
    × SR.progress (erase t) ≡ inj₁ (inj₁ {!!}))
  ⊎
  Σ (AR.Error t) λ e → AR.progress t ≡ error e
    × SR.progress (erase t) ≡ inj₁ (inj₂ {!!})
lemma t = {!!}
-}
{-
theorem : {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) → 
  -- for any n such that eval terminates with a value, then run also terminates with the erasure of the same value
  ∀ n → (p : Σ (∅ ⊢ A) λ t' → Σ (t AR.—↠ t') λ p → Σ (AR.Value t') λ v → eval (gas n) t ≡ steps p (done t' v))
  → proj₁ (run (erase t) n) ≡ erase (proj₁ p) × Σ (SR.Value (proj₁ (run (erase t) n))) λ v → proj₂ (proj₂ (run (erase t) n)) ≡ inj₁ (just v)
  -- question: is the last clause needed?
theorem t (suc n) (t' P., p P., v P., q) with AR.progress t | SR.progress (erase t)
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₁ q' = {!!}
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₂ y = {!!}
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₁ v'') = refl P., (v'' P., refl)
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₂ e) = refl P., {!!} -- missing info, I would need that something reduces to e...
theorem t (suc n) (t' P., p P., v P., q) | done x | inj₂ y = {!!}
-}
\end{code}
