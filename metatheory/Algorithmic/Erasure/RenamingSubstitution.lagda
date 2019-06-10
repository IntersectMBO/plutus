\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Untyped
import Untyped.RenamingSubstitution as U

open import Data.Fin
import Data.Product as P
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∋_)
\end{code}

\begin{code}
backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → Fin (len Γ) → Φ ⊢Nf⋆ *
backVar⋆ (Γ ,⋆ J) x = weakenNf (backVar⋆ Γ x)
backVar⋆ (Γ , A) zero    = A
backVar⋆ (Γ , A) (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(i : Fin (len Γ)) → Γ ∋ (backVar⋆ Γ i)
backVar (Γ ,⋆ J) x      = T (backVar Γ x)
backVar (Γ , A) zero    = Z
backVar (Γ , A) (suc x) = S (backVar Γ x)

{-
backVar-eraseVar : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A)
  → P.Σ (P.proj₁ (backVar {Γ = Γ} (eraseVar x)) ≡ A)
        λ p → subst (Γ ∋_) p (P.proj₂ (backVar {Γ = Γ} (eraseVar x))) ≡ x
backVar-eraseVar Z = refl P., refl
backVar-eraseVar (S i) = let p P., q = backVar-eraseVar i in
  p P., trans {!!} (cong S q)
backVar-eraseVar (T i) = {!!}

--

erase-Ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{ρ⋆ : ⋆.Ren Φ Ψ}
  → A.Ren ρ⋆ Γ Δ → U.Ren (len Γ) (len Δ) 
erase-Ren ρ i = eraseVar (ρ (P.proj₂ (backVar i)))

--

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → A.Sub σ⋆ Γ Δ → U.Sub (len Γ) (len Δ) 
erase-Sub σ⋆ σ i = erase (σ (P.proj₂ (backVar i)))

sub-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.subst σ⋆ σ t) ≡ U.sub (erase-Sub σ⋆ σ) (erase t) 
sub-erase σ⋆ σ (` x) = {!cong (erase ∘ σ) ? !}
sub-erase σ⋆ σ (ƛ x t) = cong (ƛ x)
  (trans (sub-erase σ⋆ (A.exts σ⋆ σ) t)
         {!!})
sub-erase σ⋆ σ (t · u) = {!!}
sub-erase σ⋆ σ (Λ x t) = {!!}
sub-erase σ⋆ σ (t ·⋆ A) = {!!}
sub-erase σ⋆ σ (wrap1 pat arg t) = {!!}
sub-erase σ⋆ σ (unwrap1 t) = {!!}
sub-erase σ⋆ σ (con x) = {!!}
sub-erase σ⋆ σ (builtin bn σ₁ ts) = {!!}
sub-erase σ⋆ σ (error A) = {!!}
  
lem[]⋆ : ∀{Φ}{Γ : Ctx Φ}{K}{B : Φ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{A : Φ ⊢Nf⋆ K}
  → erase N ≡ erase (N A.[ A ]⋆)
lem[]⋆ = {!!}

lem[] : ∀{Φ}{Γ : Ctx Φ}{A B : Φ ⊢Nf⋆ *}{N : Γ , A ⊢ B}{W : Γ ⊢ A}
  → erase N U.[ erase W ] ≡ erase (N A.[ W ])
lem[] = {!!}
-}
\end{code}
