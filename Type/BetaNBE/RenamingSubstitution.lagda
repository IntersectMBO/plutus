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

reify ∘ reflect preserves the neutral term

\begin{code}
reify-reflect : ∀{K Φ}(n : Φ ⊢NeN⋆ K) → reify (reflect n) ≡ ne n
reify-reflect {#}     n = refl
reify-reflect {*}     n = refl
reify-reflect {K ⇒ J} n = refl
\end{code}

eval is closed under propositional equality for terms

\begin{code}
evalCRSubst : ∀{Φ Ψ K}{η η' : Env Φ Ψ}
  → EnvCR η η'
  → {t t' : Φ ⊢⋆ K}
  → t ≡ t'
  → CR K (eval t η) (eval t' η')
evalCRSubst p {t = t} refl = idext p t
\end{code}

Substitution for normal forms:
1. embed back into syntax;
2. perform substitution;
3. renormalize.

\begin{code}
substNf : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
substNf ρ n = nf (subst (embNf ∘ ρ) (embNf n))
\end{code}

First monad law for substnf

\begin{code}
substNf-id : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → substNf (ne ∘ `) n ≡ n
substNf-id n = trans (cong nf (subst-id (embNf n))) (stability n)
\end{code}

Two lemmas that aim to remove a superfluous additional normalisation
via stability

\begin{code}
substNf-nf : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
    -------------------------------------------
  → nf (subst (embNf ∘ σ) t) ≡ substNf σ (nf t)
substNf-nf σ t = trans
  (reifyCR (subst-eval t idCR (embNf ∘ σ)))
  (trans
    (sym
      (reifyCR (fund (λ x → idext idCR (embNf (σ x))) (sym≡β (soundness t)))))
    (sym (reifyCR (subst-eval (embNf (nf t)) idCR (embNf ∘ σ)))))
\end{code}

Third Monad Law for substNf

\begin{code}
substNf-comp : ∀{Φ Ψ Θ}
  (g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ⊢Nf⋆ J)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -----------------------------------------------
  → substNf (substNf f ∘ g) A ≡ substNf f (substNf g A)
substNf-comp g f A = trans
  (trans
    (trans
      (reifyCR
        (subst-eval
          (embNf A)
          idCR
          (embNf ∘ nf ∘ subst (embNf ∘ f) ∘ embNf ∘ g)))
      (trans (reifyCR
               (idext
                 (λ x → fund
                   idCR
                   (sym≡β (soundness (subst (embNf ∘ f) (embNf (g x))))))
                 (embNf A)))
             (sym
               (reifyCR
                 (subst-eval
                   (embNf A)
                   idCR
                   (subst (embNf ∘ f) ∘ embNf ∘ g))))))
  (cong nf (subst-comp (embNf A)))) (substNf-nf f (subst (embNf ∘ g) (embNf A)))
\end{code}

extending a normal substitution

\begin{code}
extsNf : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    -------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢Nf⋆ J)
extsNf σ Z      =  ne (` Z)
extsNf σ (S α)  =  weakenNf (σ α)
\end{code}

cons for normal substitutions

\begin{code}
substNf-cons : ∀{Φ Ψ}
  → (∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{J}(A : Ψ ⊢Nf⋆ J)
  → (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢Nf⋆ K)
substNf-cons σ A Z     = A
substNf-cons σ A (S x) = σ x
\end{code}

One place normal substitution

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = substNf (substNf-cons (ne ∘ `) B) A
\end{code}

Pushing renaming through a one place normal substitution

note: It might be good to prove rename ∘ substNf = ... first?

\begin{code}
rename[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          --------------------------------------------------------------
        → renameNf ρ (t [ u ]Nf) ≡ renameNf (ext ρ) t [ renameNf ρ u ]Nf
rename[]Nf ρ t u = trans
  (rename-reify
    (idext idCR (subst (embNf ∘ substNf-cons (ne ∘ `) u) (embNf t))) ρ)
  (reifyCR
    (transCR
      (transCR
        (renameVal-eval
          (subst (embNf ∘ (substNf-cons (ne ∘ `) u)) (embNf t))
          idCR
          ρ)
        (transCR
          (subst-eval
            (embNf t)
            (renCR ρ ∘ idCR)
            (embNf ∘ (substNf-cons (ne ∘ `) u)))
          (transCR
            (transCR
              (idext
                (λ { Z → transCR
                       (transCR
                         (idext (λ x → renameVal-reflect ρ (` x)) (embNf u))
                         (symCR (rename-eval (embNf u) idCR ρ)))
                       (symCR (evalCRSubst idCR (rename-embNf ρ u)))
                   ; (S x) → renameVal-reflect ρ (` x)})
                (embNf t))
              (symCR
                (rename-eval
                  (embNf t)
                  (λ z →
                    idext
                      idCR
                      (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) z)))
                  (ext ρ))))
          (evalCRSubst
            (λ x →
              idext
                idCR
                (embNf (substNf-cons (ne ∘ `) (renameNf ρ u) x)))
            (sym (rename-embNf (ext ρ) t))))))
      (symCR
        (subst-eval
          (embNf (renameNf (ext ρ) t))
          idCR
          (embNf ∘ (substNf-cons (ne ∘ `) (renameNf ρ u)))))))
\end{code}

Pushing a normal substitution through a one place normal substitution

\begin{code}
subst[]Nf : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
    --------------------------------------------------------------
  → substNf ρ (B [ A ]Nf) ≡ substNf (extsNf ρ) B [ substNf ρ A ]Nf

subst[]Nf ρ A B = trans
  (sym (substNf-comp (substNf-cons (ne ∘ `) A) ρ B))
  (trans
    (reifyCR
      (subst-eval
        (embNf B)
        idCR
        (embNf ∘ substNf ρ ∘ (substNf-cons (ne ∘ `) A))))
    (trans
      (trans
        (trans
          (reifyCR
            (idext
              (λ x → fund
                idCR
                (sym≡β
                  (soundness
                    (subst (embNf ∘ ρ) (embNf (substNf-cons (ne ∘ `) A x))))))
              (embNf B)))
          (trans
            (reifyCR
              (idext
                (λ { Z → symCR
                     (fund
                       idCR
                       (sym≡β (soundness (subst (embNf ∘ ρ) (embNf A)))))
                   ; (S x) → transCR
                        (symCR
                          (rename-eval
                            (embNf (ρ x))
                            (λ x → idext
                              idCR
                              (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x)))
                              S))
                        (symCR
                          (evalCRSubst
                            (λ y → idext
                              idCR
                              (embNf (substNf-cons (ne ∘ `) (substNf ρ A) y)))
                            (rename-embNf S (ρ x))))})
                (embNf B)))
            (sym
              (reifyCR
                (subst-eval
                  (embNf B)
                  (λ x → idext
                    idCR
                    (embNf (substNf-cons (ne ∘ `) (substNf ρ A) x)))
                  (embNf ∘ extsNf ρ))))))
        (sym
          (reifyCR
            (fund
              (λ x → idext
                idCR
                (embNf
                  (substNf-cons
                    (ne ∘ `)
                    (nf (subst (embNf ∘ ρ) (embNf A)))
                    x)))
              (sym≡β (soundness (subst (embNf ∘ extsNf ρ) (embNf B))))))))
      (sym
        (reifyCR
          (subst-eval
            (embNf (substNf (extsNf ρ) B))
            idCR
            (λ x → embNf
              (substNf-cons (ne ∘ `) (nf (subst (embNf ∘ ρ) (embNf A))) x)))))))
\end{code}

Extending a normal environment and then embedding is the same as
embedding and then extending.

\begin{code}
substNf-lemma : ∀{Φ Ψ K J}
  (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (t : Φ ,⋆ K ⊢⋆ J)
  → subst (exts (embNf ∘ ρ)) t ≡ subst (embNf ∘ extsNf ρ) t
substNf-lemma ρ t =
  subst-cong (λ { Z → refl ; (S x) → sym (rename-embNf S (ρ x))}) t
\end{code}

Repair a mismatch between two different ways of extending an environment

\begin{code}
substNf-lemma' : ∀{Φ K J}
  → (B : Φ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B ((renameVal S ∘ idEnv _) ,,⋆ fresh))
substNf-lemma' B = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S x) → symCR (renameVal-reflect S (` x))}) B)
\end{code}

combining the above lemmas

note: there are several mismatches here, one due to two different ways
of extending a normal substitution and another due to two different
ways of extending an environment

\begin{code}
subst[]Nf' : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
  → substNf ρ (B [ A ]Nf)
    ≡
    (reify (eval (subst (exts (embNf ∘ ρ)) (embNf B))
                 ((renameVal S ∘ idEnv _) ,,⋆ fresh)))
    [ substNf ρ A ]Nf
subst[]Nf' ρ A B =
  trans (subst[]Nf ρ A B)
        (trans (cong (λ t → nf t [ substNf ρ A ]Nf)
                     (sym (substNf-lemma ρ (embNf B))))
               (cong (λ n → n [ substNf ρ A ]Nf)
                     (substNf-lemma' (subst (exts (embNf ∘ ρ)) (embNf B)))))
\end{code}

