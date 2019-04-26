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
eraseK : Kind → ScopedKind
eraseK * = *
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
eraseNf⋆ (con c) = con c

eraseNe⋆ (` α) = ` (eraseVar⋆ α)
eraseNe⋆ (n · n') = eraseNe⋆ n · eraseNf⋆ n'
-- ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *
eraseNe⋆ (μ1 {K = K}) = ƛ "x"
  ((eraseK K ⇒ *) ⇒ eraseK K ⇒ *)
  (ƛ "y" (eraseK K) (μ (` (suc zero)) (` zero)))
\end{code}


\begin{code}
len : Ctx → Weirdℕ
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

open import Relation.Binary.PropositionalEquality as Eq
lem : ∀ Γ → Scoped.∥ len Γ ∥ ≡ len⋆ A.∥ Γ ∥
lem ∅ = refl
lem (Γ ,⋆ K) = cong suc (lem Γ)
lem (Γ , A) = lem Γ

eraseVar : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K} → Γ ∋ A → WeirdFin (len Γ)
eraseVar Z = Z
eraseVar (S x) = S (eraseVar x)
eraseVar (T x) = T (eraseVar x)


eraseC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → Scoped.TermCon
eraseC (integer i) = integer i
eraseC (bytestring b) = bytestring b

open import Data.List as L
open import Data.Product as P
open import Function hiding (_∋_)

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
erase {Γ} (ƛ {A = A} t) =
  ƛ "x" (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) ) (erase t)
erase (t · u) = erase t · erase u
erase (Λ {K = K} t) = Λ "x" (eraseK K) (erase t)
erase {Γ} (t ·⋆ A) = erase t ·⋆ Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) 
erase {Γ} (wrap1 pat arg t) = wrap
  (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ pat))
  (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ arg))
  (erase t)
erase (unwrap1 t) = unwrap (erase t)
erase (con c) = con (eraseC c)
erase {Γ} (builtin b σ ts) = builtin b (eraseSub' Γ σ) (eraseTel σ _ ts)
erase {Γ} (error A) = error (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) )
\end{code}
