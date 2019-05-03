\begin{code}
module Algorithmic.Erasure where
\end{code}

\begin{code}
open import Algorithmic
open import Untyped
open import Type.BetaNormal
open import Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con renaming (TermCon to TyTermCon)


open import Data.Nat
open import Data.Fin
open import Data.List
\end{code}

\begin{code}
len : ∀{Φ} → Ctx Φ → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)
\end{code}

\begin{code}
eraseVar : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{A : Φ ⊢Nf⋆ *} → TyTermCon A → TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b

open import Type.BetaNBE.RenamingSubstitution

eraseTel : ∀{Φ Γ Δ}{σ : SubNf Δ Φ}{As : List (Δ ⊢Nf⋆ *)}
  → Tel Γ Δ σ As
  → List (len Γ ⊢)
erase : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ⊢ A → len Γ ⊢

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = erase t
erase (t ·⋆ A)          = erase t
erase (wrap1 pat arg t) = erase t
erase (unwrap1 t)       = erase t
erase {Γ} (con t)       = con (eraseTC {Γ} t)
erase (builtin bn σ ts) = builtin bn (eraseTel ts)
erase (error A)         = error

open import Data.Product renaming (_,_ to _,,_)

eraseTel {As = []}     _          = []
eraseTel {As = x ∷ As} (t ,, tel) = erase t ∷ eraseTel tel
\end{code}

Porting this from declarative required basically deleting one line but
I don't think I can fully exploit this by parameterizing the module as
I need to pattern match on the term constructors

# Erasing decl/alg terms agree

\begin{code}
open import Relation.Binary.PropositionalEquality
import Declarative as D
import Declarative.Erasure as D
open import Algorithmic.Completeness

lenLemma : ∀ {Φ}(Γ : D.Ctx Φ) → len (nfCtx Γ) ≡ D.len Γ
lenLemma D.∅        = refl
lenLemma (Γ D.,⋆ J) = lenLemma Γ
lenLemma (Γ D., A)  = cong suc (lenLemma Γ)

lemzero : ∀{n n'}(p : suc n ≡ suc n') → zero ≡ subst Fin p zero
lemzero refl = refl

lemsuc : ∀{n n'}(p : suc n ≡ suc n')(q : n ≡ n')(i : Fin n) →
  suc (subst Fin q i) ≡ subst Fin p (suc i)
lemsuc refl refl i = refl

lemT : ∀{Φ J K}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ J}{A'' : Φ ,⋆ K ⊢Nf⋆ J}(p : weakenNf {K = K} A ≡ A'')(q : A ≡ A')(x : Γ ∋ A)
  → eraseVar x ≡ eraseVar (conv∋ p (T x))
lemT refl refl x = refl

open import Function

sameVar : ∀{Φ Γ J}{A : Φ ⊢⋆ J}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst Fin (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} D.Z = lemzero (cong suc (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x) = trans
  (sameVar x)
  (cong (subst Fin (lenLemma Γ)) (lemT (rename-nf S A) refl (nfTyVar x)))

{-
same : ∀{Φ Γ J}{A : Φ ⊢⋆ J}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 
same {Γ = Γ}(D.` x) = {!!}
same (D.ƛ t) = {!!}
same (t D.· t₁) = {!!}
same (D.Λ t) = {!!}
same (t D.·⋆ A) = {!!}
same (D.wrap1 pat arg t) = {!!}
same (D.unwrap1 t) = {!!}
same (D.conv x t) = {!!}
same (D.con x) = {!!}
same (D.builtin bn σ x) = {!!}
same (D.error A) = {!!}
-}
\end{code}
