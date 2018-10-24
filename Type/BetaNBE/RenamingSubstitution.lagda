\begin{code}
module Type.BetaNBE.RenamingSubstitution where

open import Type
open import Type.Equality
open import Type.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Stability

open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Function
\end{code}


\begin{code}
reify-reflect : ∀{K Γ}(n : Γ ⊢NeN⋆ K) → reify (reflect n) ≡ ne n
reify-reflect {#}     n = refl
reify-reflect {*}     n = refl
reify-reflect {K ⇒ J} n = refl
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
lemma1 : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
  → nf (subst σ t) ≡ substNf (nf ∘ σ) (nf t)
lemma1 σ t =
  trans (reifyPER _ (subst-eval t idPER σ))
        (trans (trans (reifyPER _ (fund (idext idPER ∘ σ) (soundness t)))
                      (reifyPER _ (idext (λ x → fund idPER (soundness (σ x))) (embNf (nf t)))))
               (reifyPER _ (symPER _ (subst-eval (embNf (nf t)) idPER (embNf ∘ nf ∘ σ)))))
\end{code}

\begin{code}
lemma2 : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
  → nf (subst (embNf ∘ σ) t) ≡ substNf σ (nf t)
lemma2 σ t = trans (reifyPER _ (subst-eval t idPER (embNf ∘ σ))) (trans (sym (reifyPER _ (fund (λ x → idext idPER (embNf (σ x))) (sym≡β (soundness t))))) (sym (reifyPER _ (subst-eval (embNf (nf t)) idPER (embNf ∘ σ)))))
\end{code}

monad law for substnf
\begin{code}
substNf-comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢Nf⋆ J)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -----------------------------------------------
  → substNf (substNf f ∘ g) A ≡ substNf f (substNf g A)
substNf-comp g f A = trans (trans (trans (reifyPER _ (subst-eval (embNf A) idPER (embNf ∘ nf ∘ subst (embNf ∘ f) ∘ embNf ∘ g))) (trans (reifyPER _ (idext (λ x → fund idPER (sym≡β (soundness (subst (embNf ∘ f) (embNf (g x)))))) (embNf A))) (sym (reifyPER _ (subst-eval (embNf A) idPER (subst (embNf ∘ f) ∘ embNf ∘ g)))))) (cong nf (subst-comp (embNf A)))) (lemma2 f (subst (embNf ∘ g) (embNf A)))
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
rename[]Nf ρ t u = trans (rename-reify (idext idPER (subst (embNf ∘ substNf-cons (ne ∘ `) u) (embNf t))) ρ) (reifyPER _ (transPER _ (transPER _ (renameVal-eval (subst (embNf ∘ (substNf-cons (ne ∘ `) u)) (embNf t)) idPER ρ) (transPER _ (subst-eval (embNf t) (renPER ρ ∘ idPER) (embNf ∘ (substNf-cons (ne ∘ `) u))) (transPER _ (transPER _ (idext (λ { Z → transPER _ (transPER _ (idext (λ x → renameVal-reflect ρ (` x)) (embNf u)) (symPER _ (rename-eval (embNf u) idPER ρ))) (symPER _ (evalPERSubst idPER (rename-embNf ρ u))) ; (S x) → renameVal-reflect ρ (` x)}) (embNf t)) (symPER _ (rename-eval (embNf t) (λ z → idext idPER (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) z))) (ext ρ)))) (evalPERSubst (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) x))) (sym (rename-embNf (ext ρ) t)))))) (symPER _ (subst-eval (embNf (renameNf (ext ρ) t)) idPER (embNf ∘ (substNf-cons (ne ∘ `) (renameNf ρ u))))))) 
\end{code}

\begin{code}
subst[]Nf : ∀{Γ Δ K J}
  (ρ : ∀{K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
  → (A : Γ ⊢Nf⋆ K)
  → (B : Γ ,⋆ K ⊢Nf⋆ J)
  → substNf ρ (B [ A ]Nf) ≡ substNf (extsNf ρ) B [ substNf ρ A ]Nf

subst[]Nf ρ A B =
  trans (sym (substNf-comp (substNf-cons (ne ∘ `) A) ρ B))
        (trans (reifyPER _ (subst-eval (embNf B) idPER (embNf ∘ substNf ρ ∘ (substNf-cons (ne ∘ `) A))))
               (trans (trans (trans (reifyPER _ (idext (λ x → fund idPER (sym≡β (soundness (subst (embNf ∘ ρ) (embNf (substNf-cons (ne ∘ `) A x)))))) (embNf B)))
                                    (trans (reifyPER _ (idext (λ { Z → symPER _ (fund idPER (sym≡β (soundness (subst (embNf ∘ ρ) (embNf A)))))
                                                              ; (S x) → transPER _ (symPER _ (rename-eval (embNf (ρ x)) (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x))) S))
                                                                                   (symPER _ (evalPERSubst (λ y → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) y))) (rename-embNf S (ρ x))))}) (embNf B)))
                                           (sym (reifyPER _ (subst-eval (embNf B) (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x))) (embNf ∘ extsNf ρ))))))
                             (sym (reifyPER _ (fund (λ x → idext idPER (embNf (substNf-cons (ne ∘ `) (nf (subst (embNf ∘ ρ) (embNf A))) x))) (sym≡β (soundness (subst (embNf ∘ extsNf ρ) (embNf B))))))))
                      (sym (reifyPER _ (subst-eval (embNf (substNf (extsNf ρ) B)) idPER (λ x → embNf (substNf-cons (ne ∘ `) (nf (subst (embNf ∘ ρ) (embNf A))) x))))))) 
\end{code}

-- this stuff is just to make things when defining subsitution for terms
\begin{code}
substNf-lemma : ∀{Γ Δ K J}
  (ρ : ∀{K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
  → (t : Γ ,⋆ K ⊢⋆ J)
  → subst (exts (embNf ∘ ρ)) t ≡ subst (embNf ∘ extsNf ρ) t
substNf-lemma ρ t = subst-cong (λ { Z → refl ; (S x) → sym (rename-embNf S (ρ x))}) t
\end{code}

\begin{code}
substNf-lemma' : ∀{Γ K J}
  → (B : Γ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B ((renameVal S ∘ idEnv _) ,,⋆ fresh))
substNf-lemma' B = reifyPER _ (idext (λ { Z → reflectPER _ refl ; (S x) → symPER _ (renameVal-reflect S (` x))}) B)
\end{code}

\begin{code}
subst[]Nf' : ∀{Γ Δ K J}
  (ρ : ∀{K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
  → (A : Γ ⊢Nf⋆ K)
  → (B : Γ ,⋆ K ⊢Nf⋆ J)
  → substNf ρ (B [ A ]Nf) ≡ (reify (eval (subst (exts (embNf ∘ ρ)) (embNf B)) ((renameVal S ∘ idEnv _) ,,⋆ fresh))) [ substNf ρ A ]Nf
subst[]Nf' ρ A B =
  trans (subst[]Nf ρ A B)
        (trans (cong (λ t → nf t [ substNf ρ A ]Nf) (sym (substNf-lemma ρ (embNf B))))
               (cong (λ n → n [ substNf ρ A ]Nf) (substNf-lemma' (subst (exts (embNf ∘ ρ)) (embNf B)))))
\end{code}

