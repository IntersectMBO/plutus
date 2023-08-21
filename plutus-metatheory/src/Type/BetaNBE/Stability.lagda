\begin{code}
module Type.BetaNBE.Stability where
\end{code}

\begin{code}
open import Data.Vec using (Vec;[];_∷_)
open import Data.List using (List;[];_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;cong;cong₂)

open import Utils using (*;♯;_⇒_;K)
open import Type using (Ctx⋆;Φ;Z;S)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;embNe;embNf-List;embNf-VecList)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (nf;idEnv;eval;reflect;eval-List;eval-VecList)
open import Type.BetaNBE.Completeness using (CR;idext;reifyCR;reflectCR;transCR;idCR;AppCR;renVal-reflect)
\end{code}

If you take a normal form, embed it back into syntax and then
normalize it again, you get the same result. This is an important
property for substitution on normal forms: we don't want to eta expand
variables otherwise substituting in by the identity substitution can
perturb the expression.

\begin{code}
stability : ∀{K}(n : Φ ⊢Nf⋆ K) → nf (embNf n) ≡ n
stabilityNe : (n : Φ ⊢Ne⋆ K) → CR K (eval (embNe n) (idEnv _)) (reflect n)

stability-List : ∀(xs : List (Φ ⊢Nf⋆ *)) → 
  eval-List (embNf-List xs) (λ x → reflect (` x)) ≡ xs
stability-VecList : ∀{n}(xss : Vec (List (Φ ⊢Nf⋆ *)) n) → 
  eval-VecList (embNf-VecList xss) (λ x → reflect (` x)) ≡ xss

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
stability (con c) = cong con (stability c)
stability (μ A B) = cong₂ μ (stability A) (stability B)
stability {K = *} (ne n) = stabilityNe n
stability {K = ♯} (ne n) = stabilityNe n
stability {K = K ⇒ J} (ne n) = reifyCR (stabilityNe n)
stability (SOP xss) = cong SOP (stability-VecList xss)

stabilityNe (` α) = reflectCR refl
stabilityNe (^ x) = reflectCR refl
stabilityNe (n · n') = transCR
  (AppCR (stabilityNe n) (idext idCR (embNf n')))
  (reflectCR (cong₂ _·_ refl (stability n')))

stability-List [] = refl
stability-List (x ∷ xs) = cong₂ _∷_ (stability x) (stability-List xs)
stability-VecList [] = refl
stability-VecList (xs ∷ xss) = cong₂ _∷_ (stability-List xs) (stability-VecList xss)
\end{code}
