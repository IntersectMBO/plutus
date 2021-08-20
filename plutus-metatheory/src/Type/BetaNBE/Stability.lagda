\begin{code}
module Type.BetaNBE.Stability where
\end{code}

\begin{code}
open import Utils
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)

open import Relation.Binary.PropositionalEquality
open import Function
\end{code}

If you take a normal form, embed it back into syntax and then
normalize it again, you get the same result. This is an important
property for substitution on normal forms: we don't want to eta expand
variables otherwise substituting in by the identity substitution can
perturb the expression.

\begin{code}
stability : ∀{K}(n : Φ ⊢Nf⋆ K) → nf (embNf n) ≡ n
stabilityTyCon : (c : TyCon Φ) → evalTyCon (embNfTyCon c) (idEnv _) ≡ c
stabilityTyCon integer    = refl
stabilityTyCon bytestring = refl
stabilityTyCon string     = refl
stabilityTyCon unit       = refl
stabilityTyCon bool       = refl
stabilityTyCon (list A)   = cong list (stability A)
stabilityTyCon (pair A B) = cong₂ pair (stability A) (stability B)
stabilityTyCon Data       = refl

stabilityNe : (n : Φ ⊢Ne⋆ K) → CR K (eval (embNe n) (idEnv _)) (reflect n)

stability (Π B) =
  cong Π (trans (idext (λ { Z → reflectCR refl
                          ; (S α) → renVal-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (A ⇒ B) = cong₂ _⇒_ (stability A) (stability B)
stability (ƛ B) =
  cong ƛ (trans (reifyCR (idext (λ { Z → reflectCR refl
                                      ; (S α) → renVal-reflect S (` α)})
                                   (embNf B)))
                (stability B))
stability (con c) = cong con (stabilityTyCon c)
stability (μ A B) = cong₂ μ (stability A) (stability B)
stability {K = *} (ne n) = stabilityNe n
stability {K = K ⇒ J} (ne n) = reifyCR (stabilityNe n)

stabilityNe (` α) = reflectCR refl
stabilityNe (n · n') = transCR
  (AppCR (stabilityNe n) (idext idCR (embNf n')))
  (reflectCR (cong₂ _·_ refl (stability n')))
\end{code}
