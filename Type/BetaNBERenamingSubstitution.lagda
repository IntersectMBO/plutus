\begin{code}
module Type.BetaNBERenamingSubstitution where

open import Type
open import Type.Equality
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.RenamingSubstitution

open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Function
\end{code}

\begin{code}
evalSubst : ∀{Γ Δ K}{η : Env Γ Δ}{t t' : Γ ⊢⋆ K} → t ≡ t' → eval t η ≡ eval t' η
evalSubst refl = refl

evalPERSubst : ∀{Γ Δ K}{η η' : Env Γ Δ} → PEREnv η η' → {t t' : Γ ⊢⋆ K} → t ≡ t' → PER K (eval t η) (eval t' η')
evalPERSubst p {t = t} refl = idext p t
\end{code}

\begin{code}
substNf : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
substNf ρ n = nf (subst (embNf ∘ ρ) (embNf n))
\end{code}

first monad law for substnf
\begin{code}
substNf-id : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → substNf (ne ∘ `) n ≡ n
substNf-id n = trans (cong nf (subst-id (embNf n))) (stability n)
\end{code}

\begin{code}
postulate soundness : ∀ {Φ J} → (t : Φ ⊢⋆ J) → embNf (nf t) ≡β t
\end{code}

\begin{code}
lemma1 : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
  → nf (subst σ t) ≡ substNf (nf ∘ σ) (nf t)
lemma1 σ t =
  trans (reify _ (subst-eval t idPER σ))
        (trans (trans (reify _ (fund (idext idPER ∘ σ) (sym≡β (soundness t))))
                      (reify _ (idext (λ x → fund idPER (sym≡β (soundness (σ x)))) (embNf (nf t)))))
               (reify _ (symPER _ (subst-eval (embNf (nf t)) idPER (embNf ∘ nf ∘ σ)))))
\end{code}

\begin{code}
lemma2 : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
  → nf (subst (embNf ∘ σ) t) ≡ substNf σ (nf t)
lemma2 σ t = trans (reify _ (subst-eval t idPER (embNf ∘ σ))) (trans (sym (reify _ (fund (λ x → idext idPER (embNf (σ x))) (soundness t)))) (sym (reify _ (subst-eval (embNf (nf t)) idPER (embNf ∘ σ)))))
\end{code}

monad law for substnf
\begin{code}
substNf-comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢Nf⋆ J)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -----------------------------------------------
  → substNf (substNf f ∘ g) A ≡ substNf f (substNf g A)
substNf-comp g f A = trans (trans (trans (reify _ (subst-eval (embNf A) idPER (embNf ∘ nf ∘ subst (embNf ∘ f) ∘ embNf ∘ g))) (trans (reify _ (idext (λ x → fund idPER (soundness (subst (embNf ∘ f) (embNf (g x))))) (embNf A))) (sym (reify _ (subst-eval (embNf A) idPER (subst (embNf ∘ f) ∘ embNf ∘ g)))))) (cong nf (subst-comp (embNf ∘ g) (embNf ∘ f) (embNf A)))) (lemma2 f (subst (embNf ∘ g) (embNf A)))
\end{code}


\begin{code}
extsNf : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢Nf⋆ J)
extsNf σ Z      =  ne (` Z)
extsNf σ (S α)  =  weakenNf (σ α)
\end{code}

\begin{code}
substNf-cons : ∀{Φ Ψ} → (∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K) → ∀{J}(A : Ψ ⊢Nf⋆ J) →
             (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢Nf⋆ K)
substNf-cons σ A Z     = A
substNf-cons σ A (S x) = σ x
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = substNf (substNf-cons (ne ∘ `) B) A
\end{code}

\begin{code}
rename[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          ------
        → renameNf ρ (t [ u ]Nf) ≡ renameNf (ext ρ) t [ renameNf ρ u ]Nf
rename[]Nf ρ t u = trans (rename-readback (idext idPER (subst (embNf ∘ substNf-cons (ne ∘ `) u) (embNf t))) ρ) (reify _ (transPER _ (transPER _ (renval-eval (subst (embNf ∘ (substNf-cons (ne ∘ `) u)) (embNf t)) idPER ρ) (transPER _ (subst-eval (embNf t) (renPER ρ ∘ idPER) (embNf ∘ (substNf-cons (ne ∘ `) u))) (transPER _ (transPER _ (idext (λ { Z → transPER _ (transPER _ (idext (λ x → renval-neV ρ (` x)) (embNf u)) (symPER _ (rename-eval (embNf u) idPER ρ))) (symPER _ (evalPERSubst idPER (rename-embNf ρ u))) ; (S x) → renval-neV ρ (` x)}) (embNf t)) (symPER _ (rename-eval (embNf t) (λ z → idext idPER (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) z))) (ext ρ)))) (evalPERSubst (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) x))) (sym (rename-embNf (ext ρ) t)))))) (symPER _ (subst-eval (embNf (renameNf (ext ρ) t)) idPER (embNf ∘ (substNf-cons (ne ∘ `) (renameNf ρ u))))))) 
\end{code}

\begin{code}
subst[]Nf : ∀{Γ Δ K J}
  (ρ : ∀{K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
  → (A : Γ ⊢Nf⋆ K)
  → (B : Γ ,⋆ K ⊢Nf⋆ J)
  → substNf ρ (B [ A ]Nf) ≡ substNf (extsNf ρ) B [ substNf ρ A ]Nf
subst[]Nf ρ A B =
  trans (sym (substNf-comp (substNf-cons (ne ∘ `) A) ρ B))
        (trans (reify _ (subst-eval (embNf B) idPER (embNf ∘ substNf ρ ∘ (substNf-cons (ne ∘ `) A))))
               (trans (trans (trans (reify _ (idext (λ x → fund idPER (soundness (subst (embNf ∘ ρ) (embNf (substNf-cons (ne ∘ `) A x))))) (embNf B)))
                                    (trans (reify _ (idext (λ { Z → symPER _ (fund idPER (soundness (subst (embNf ∘ ρ) (embNf A))))
                                                              ; (S x) → transPER _ (symPER _ (rename-eval (embNf (ρ x)) (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x))) S))
                                                                                   (symPER _ (evalPERSubst (λ y → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) y))) (rename-embNf S (ρ x))))}) (embNf B)))
                                           (sym (reify _ (subst-eval (embNf B) (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x))) (embNf ∘ extsNf ρ))))))
                             (sym (reify _ (fund (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (nf (subst (embNf ∘ ρ) (embNf A))) x))) (soundness (subst (embNf ∘ extsNf ρ) (embNf B)))))))
                      (sym (reify _ (subst-eval (embNf (substNf (extsNf ρ) B)) idPER (λ x → embNf (substNf-cons (ne ∘ `) (nf (subst (embNf ∘ ρ) (embNf A))) x))))))) 
\end{code}
