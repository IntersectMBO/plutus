\begin{code}
module Scoped.Extrication where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic as A
open import Scoped
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as B
open import Data.Nat
open import Data.Fin
open import Type.BetaNormal
open import Type.RenamingSubstitution as T
\end{code}

type level

\begin{code}
len⋆ : Ctx⋆ → ℕ
len⋆ ∅ = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

-- scoped kind clearly shoud go...
extricateK : Kind → ScopedKind
extricateK * = *
extricateK (K ⇒ J) = extricateK K ⇒ extricateK J

extricateVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
extricateVar⋆ Z     = zero
extricateVar⋆ (S α) = suc (extricateVar⋆ α)

extricateNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
extricateNe⋆ : ∀{Γ K}(A : Γ ⊢NeN⋆ K) → ScopedTy (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateNf⋆ (Π {K = K} A) = Π "x" (extricateK K) (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B) = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} A) = ƛ "x" (extricateK K) (extricateNf⋆ A)
extricateNf⋆ (ne n) = extricateNe⋆ n
extricateNf⋆ (con c) = con c

extricateNe⋆ (` α) = ` (extricateVar⋆ α)
extricateNe⋆ (n · n') = extricateNe⋆ n · extricateNf⋆ n'
-- ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *
extricateNe⋆ (μ1 {K = K}) = ƛ "x"
  ((extricateK K ⇒ *) ⇒ extricateK K ⇒ *)
  (ƛ "y" (extricateK K) (μ (` (suc zero)) (` zero)))
\end{code}


\begin{code}
len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

open import Relation.Binary.PropositionalEquality as Eq
{-lem : ∀ {Φ}(Γ : Ctx Φ) → len Γ ≡ len⋆ Φ
lem ∅ = refl
lem (Γ ,⋆ K) = cong suc (lem Γ)
lem (Γ , A) = lem Γ
-}
extricateVar : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ∋ A → WeirdFin (len Γ)
extricateVar Z = Z
extricateVar (S x) = S (extricateVar x)
extricateVar (T x) = T (extricateVar x)


extricateC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → Scoped.TermCon
extricateC (integer i) = integer i
extricateC (bytestring b) = bytestring b

open import Data.List as L
open import Data.Product as P
open import Function hiding (_∋_)

extricateSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J) → List (ScopedTy (len⋆ Γ))
extricateSub {Δ = ∅} σ = []
extricateSub {Δ = Δ ,⋆ K} σ =
  extricateSub {Δ = Δ} (σ ∘ S) ++ L.[ extricateNf⋆ (σ Z) ]

extricateTel : ∀ {Φ Γ Δ}(σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)(as : List (Δ ⊢Nf⋆ *))
  → Tel Γ Δ σ as
  → List (ScopedTm (len Γ))
extricate : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ⊢ A → ScopedTm (len Γ)

extricateTel σ [] x = []
extricateTel σ (A ∷ As) (t P., ts) = extricateTel σ As ts ++ L.[ extricate t ]

extricate (` x) = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} x t) = ƛ x (extricateNf⋆ A) (extricate t)
extricate (t · u) = extricate t · extricate u
extricate (Λ {K = K} x t) = Λ x (extricateK K) (extricate t)
extricate {Φ}{Γ} (t ·⋆ A) = extricate t ·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap1 pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg)
  (extricate t)
extricate (unwrap1 t) = unwrap (extricate t)
extricate (con c) = con (extricateC c)
extricate {Φ}{Γ} (builtin b σ ts) =
  builtin b (extricateSub σ) (extricateTel σ _ ts)
extricate {Φ}{Γ} (error A) = error (extricateNf⋆ A)
\end{code}
