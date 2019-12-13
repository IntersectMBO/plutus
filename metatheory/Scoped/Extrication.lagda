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

extricateVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
extricateVar⋆ Z     = zero
extricateVar⋆ (S α) = suc (extricateVar⋆ α)

extricateNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
extricateNe⋆ : ∀{Γ K}(A : Γ ⊢Ne⋆ K) → ScopedTy (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateNf⋆ (Π {K = K} x A) = Π K (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B) = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} x A) = ƛ K (extricateNf⋆ A)
extricateNf⋆ (ne n) = extricateNe⋆ n
extricateNf⋆ (con c) = con c

extricateNe⋆ (` α) = ` (extricateVar⋆ α)
extricateNe⋆ (n · n') = extricateNe⋆ n · extricateNf⋆ n'
-- ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *
extricateNe⋆ (μ1 {K = K}) = ƛ 
  ((K ⇒ *) ⇒ K ⇒ *)
  (ƛ (K) (μ (` (suc zero)) (` zero)))
\end{code}


\begin{code}
len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

open import Relation.Binary.PropositionalEquality as Eq

extricateVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → WeirdFin (len Γ)
extricateVar (Z _) = Z
extricateVar (S x) = S (extricateVar x)
extricateVar (T x _) = T (extricateVar x)

extricateC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → Scoped.TermCon
extricateC (integer i)    = integer i
extricateC (bytestring b) = bytestring b
extricateC (string s)     = string s

open import Data.List as L
open import Data.Product as P
open import Function hiding (_∋_)

extricateSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J) → List (ScopedTy (len⋆ Γ))
extricateSub {Δ = ∅} σ = []
extricateSub {Δ = Δ ,⋆ K} σ =
  extricateSub {Δ = Δ} (σ ∘ S) ++ L.[ extricateNf⋆ (σ Z) ]

extricateTyL : ∀{Φ} → List (Φ ⊢Nf⋆ *) → List (ScopedTy (len⋆ Φ))
extricateTyL []       = []
extricateTyL (A ∷ As) = extricateNf⋆ A ∷ extricateTyL As

extricateTel : ∀ {Φ Γ Δ}(σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)(as : List (Δ ⊢Nf⋆ *))
  → Tel Γ Δ σ as
  → List (ScopedTm (len Γ))
extricate : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → ScopedTm (len Γ)

extricateTel σ [] x = []
extricateTel σ (A ∷ As) (t P., ts) = extricate t ∷ extricateTel σ As ts

extricate (` x) = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} x t) = ƛ (extricateNf⋆ A) (extricate t)
extricate (t · u) = extricate t · extricate u
extricate (Λ {K = K} x t) = Λ K (extricate t)
extricate {Φ}{Γ} (·⋆ t A _) = extricate t ScopedTm.·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap1 pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg)
  (extricate t)
extricate (unwrap1 t _) = unwrap (extricate t)
extricate (con c) = con (extricateC c)
extricate {Φ}{Γ} (builtin b σ ts _) =
  builtin b (extricateSub σ) (extricateTel σ _ ts)
extricate {Φ}{Γ} (error A) = error (extricateNf⋆ A)
\end{code}
