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

If you take a normal form, embed it back into syntax and then
normalize it again, you get the same result. This is an important
property for substitution on normal forms: we don't want to eta expand
variables otherwise substituting in by the identity substitution can
perturb the expression.

\begin{code}
stability : ∀{Φ K}(n : Φ ⊢Nf⋆ K) → nf (embNf n) ≡ n
stabilityNeN : ∀{Φ K}(n : Φ ⊢NeN⋆ K) → eval (embNeN n) (idEnv _)  ≡ reflect n

stability (Π B) =
  cong Π (trans (idext (λ { Z → reflectCR refl
                          ; (S α) → renameVal-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (A ⇒ B) = cong₂ _⇒_ (stability A) (stability B)
stability (ƛ B)    =
  cong ƛ (trans (reifyCR (idext (λ { Z → reflectCR refl
                                      ; (S α) → renameVal-reflect S (` α)})
                                   (embNf B)))
                (stability B))
stability (size⋆ n)   = refl
stability (con tcn s) = cong (con tcn) (stability s)
stability {K = *}     (ne n) = stabilityNeN n
stability {K = #}     (ne n) = stabilityNeN n
stability {K = K ⇒ J} (ne n) = cong (λ v → reify v) (stabilityNeN n)

stabilityNeN (` α)    = refl
stabilityNeN (n · n') =
  trans (cong (_·V (eval (embNf n') (idEnv _))) (stabilityNeN n))
        (cong (λ n'' → reflect (n · n'')) (stability n'))
stabilityNeN μ1      = refl
\end{code}
