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
stabilityNe : ∀{Φ K}(n : Φ ⊢Ne⋆ K) → eval (embNe n) (idEnv _)  ≡ reflect n

stability (Π x B) =
  cong (Π x) (trans (idext (λ { Z → reflectCR refl
                          ; (S α) → renVal-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (A ⇒ B) = cong₂ _⇒_ (stability A) (stability B)
stability (ƛ x B)    =
  cong (ƛ x) (trans (reifyCR (idext (λ { Z → reflectCR refl
                                      ; (S α) → renVal-reflect S (` α)})
                                   (embNf B)))
                (stability B))
stability (con tcn)   = refl
stability {K = *}     (ne n) = stabilityNe n
stability {K = K ⇒ J} (ne n) = cong (λ v → reify v) (stabilityNe n)

stabilityNe (` α)    = refl
stabilityNe (n · n') =
  trans (cong (_·V (eval (embNf n') (idEnv _))) (stabilityNe n))
        (cong (λ n'' → reflect (n · n'')) (stability n'))
stabilityNe μ1      = refl
\end{code}
