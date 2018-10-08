\begin{code}
module Type.BetaNBE.Stability where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness

open import Relation.Binary.PropositionalEquality
open import Function
\end{code}

\begin{code}
mutual
  stability : ∀{Γ K}(n : Γ ⊢Nf⋆ K) → nf (embNf n) ≡ n
  stability (Π B) = cong Π (trans (idext (λ { Z → reflect _ refl ; (S x) → renval-neV S (` x)}) (embNf B))
                                  (stability B))
  stability (A ⇒ B) = cong₂ _⇒_ (stability A) (stability B)
  stability (ƛ B) = cong ƛ (trans (reify _ (idext (λ { Z → reflect _ refl ; (S x) → renval-neV S (` x)}) (embNf B)))
                                  (stability B))
  stability {K = *} (ne n) = stabilityNeN n
  stability {K = K ⇒ J} (ne n) = cong (λ v → readback v) (stabilityNeN n)

  stabilityNeN : ∀{Γ K}(n : Γ ⊢NeN⋆ K) → eval (embNeN n) (idEnv _)  ≡ neV n
  stabilityNeN {K = *} (` x) = refl
  stabilityNeN {K = K ⇒ K₁} (` x) = refl
  stabilityNeN (n · n') = trans (cong (_·V (eval (embNf n') (idEnv _))) (stabilityNeN n))
                                (cong (λ n'' → neV (n · n'')) (stability n'))
  stabilityNeN (μ B) =
    cong (neV ∘ μ)
         (trans (reify _ (idext (λ { Z → reflect _ refl
                                   ; (S x) → renval-neV S (` x)}) (embNf B)))
                (stability B))
\end{code}
