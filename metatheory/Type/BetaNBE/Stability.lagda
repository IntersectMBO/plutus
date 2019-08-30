\begin{code}
module Type.BetaNBE.Stability where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
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
stability : ∀{Φ K}(n : Φ ⊢Nf⋆ K) → nf (embNf n) ≡Nf n
stabilityNe : ∀{Φ K}(n : Φ ⊢Ne⋆ K) → CR K (eval (embNe n) (idEnv _)) (reflect n)

stability (Π x B) =
  Π≡Nf (transNf (idext (λ { Z → reflectCR (var≡Ne refl)
                          ; (S α) → renVal-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (A ⇒ B) = ⇒≡Nf (stability A) (stability B)
stability (ƛ x B)    =
  ƛ≡Nf (transNf (reifyCR (idext (λ { Z → reflectCR (var≡Ne refl)
                                      ; (S α) → renVal-reflect S (` α)})
                                   (embNf B)))
                (stability B))
stability (con tcn)   = con≡Nf
stability {K = *}     (ne n) = stabilityNe n
stability {K = K ⇒ J} (ne n) = reifyCR (stabilityNe n)

stabilityNe (` α)    = reflectCR (var≡Ne refl)
stabilityNe (n · n') = transCR (AppCR (stabilityNe n) (idext idCR (embNf n'))) (reflectCR (·≡Ne reflNe (stability n')))
stabilityNe μ1      = μ≡Ne
\end{code}
