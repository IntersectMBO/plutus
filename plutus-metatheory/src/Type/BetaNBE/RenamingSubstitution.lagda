\begin{code}
module Type.BetaNBE.RenamingSubstitution where

open import Type
open import Type.Equality
open import Type.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Stability

open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Function
\end{code}


Renaming is defined in the file Type.BetaNormal as it used in the
NBE algorithm.

reify ∘ reflect preserves the neutral term

\begin{code}
reify-reflect : ∀{K Φ}(n : Φ ⊢Ne⋆ K) → reify (reflect n) ≡ ne n
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
evalCRSubst p {t = t} q = fund p (≡2β q) 
\end{code}

\begin{code}
ren-nf : ∀{ϕ ψ K}(σ : Ren ϕ ψ)(A : ϕ ⊢⋆ K) →
  renNf σ (nf A) ≡ nf (ren σ A)
ren-nf σ A = trans
  (ren-reify (idext idCR A) σ)
  (reifyCR
    (transCR
      (renVal-eval A idCR σ)
      (transCR
        (idext (renVal-reflect σ ∘ `) A)
        (symCR (ren-eval A idCR σ))  )))
\end{code}

\begin{code}
ren-nf-μ : ∀ {Φ Ψ}{K}
  → (ρ⋆ : Ren Φ Ψ)
  → (A  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (B  : Φ ⊢Nf⋆ K)
  → renNf ρ⋆
    (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
    ≡
    nf
    (embNf (renNf ρ⋆ A) · ƛ (μ (embNf (weakenNf (renNf ρ⋆ A))) (` Z)) ·
     embNf (renNf ρ⋆ B))
ren-nf-μ ρ⋆ A B = trans
  (ren-nf ρ⋆ (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  (trans
    (cong₂
      (λ X Y → nf (X · ƛ (μ (ren (ext ρ⋆) (embNf (weakenNf A))) (` Z)) · Y))
      (sym (ren-embNf ρ⋆ A))
      (sym (ren-embNf ρ⋆ B)))
    (trans
      (cong
        (λ X → nf (embNf (renNf ρ⋆ A) · ƛ (μ (ren (ext ρ⋆) X) (` Z)) · embNf (renNf ρ⋆ B)))
        (ren-embNf S A))
      (cong
        (λ X → nf (embNf (renNf ρ⋆ A) · ƛ (μ X (` Z)) · embNf (renNf ρ⋆ B)))
        (trans
          (sym (ren-comp (embNf A)))
          (trans (sym (ren-embNf (S ∘ ρ⋆) A)) (cong embNf (renNf-comp A)))))))
\end{code}

\begin{code}
SubNf : Ctx⋆ → Ctx⋆ → Set
SubNf φ Ψ = ∀ {J} → φ ∋⋆ J → Ψ ⊢Nf⋆ J
\end{code}

Substitution for normal forms:
1. embed back into syntax;
2. perform substitution;
3. renormalize.

\begin{code}
substNf : ∀ {Φ Ψ}
  → SubNf Φ Ψ
    -------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
substNf ρ n = nf (subst (embNf ∘ ρ) (embNf n))
\end{code}

First monad law for substNf

\begin{code}
substNf-id : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → substNf (ne ∘ `) n ≡ n
substNf-id n = trans
  (reifyCR (fund idCR (≡2β (subst-id (embNf n)))))
  (stability n)
\end{code}

This version of the first monad law might be η compatible as it doesn't rely
on subst-id

\begin{code}
substNf-id' : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → substNf (nf ∘ `) n ≡ n
substNf-id' n = trans
  (reifyCR
    (transCR
      (subst-eval (embNf n) idCR (embNf ∘ nf ∘ `))
      (idext
        (λ α → fund idCR (≡2β (cong embNf (stability (ne (` α))))))
        (embNf n))))
  (stability n)
\end{code}

Second monad law for substNf
This is often holds definitionally for substitution (e.g. subst) but not here.

\begin{code}
substNf-∋ : ∀ {Φ Ψ J}
  → (ρ : SubNf Φ Ψ)
  → (α : Φ ∋⋆ J)
  → substNf ρ (ne (` α)) ≡ ρ α
substNf-∋ ρ α = stability (ρ α) 
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
  (g : SubNf Φ Ψ)
  (f : SubNf Ψ Θ)
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
    (completeness (≡2β (subst-comp (embNf A)))))
  (substNf-nf f (subst (embNf ∘ g) (embNf A)))
\end{code}

extending a normal substitution

\begin{code}
extsNf : ∀ {Φ Ψ}
  → SubNf Φ Ψ
    -------------------------------
  → ∀ {K} → SubNf (Φ ,⋆ K) (Ψ ,⋆ K)
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

Substitution of one variable

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = substNf (substNf-cons (ne ∘ `) B) A
\end{code}

Congruence lemma for subst
\begin{code}
substNf-cong : ∀ {Φ Ψ}
  → {f g : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Nf⋆ K)
    -------------------------------
  → substNf f A ≡ substNf g A
substNf-cong p A =
 reifyCR (fund idCR (≡2β (subst-cong (cong embNf ∘ p ) (embNf A))))
\end{code}

\begin{code}
substNf-cong' : ∀ {Φ Ψ}
  → (f : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{K}{A A' : Φ ⊢Nf⋆ K}
  → A ≡ A'
    -------------------------------
  → substNf f A ≡ substNf f A'
substNf-cong' f p = cong (substNf f) p
\end{code}

Pushing renaming through normal substitution

\begin{code}
renNf-substNf : ∀{Φ Ψ Θ}
  → (g : SubNf Φ Ψ)
  → (f : Ren Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
   -----------------------------------------------------
  → substNf (renNf f ∘ g) A ≡ renNf f (substNf g A)
renNf-substNf g f A = trans
  (reifyCR
    (transCR
      (transCR
        (subst-eval (embNf A) idCR (embNf ∘ renNf f ∘ g))
        (transCR
          (idext
            (λ α → transCR
              (evalCRSubst idCR (ren-embNf f (g α)))
              (transCR
                (ren-eval (embNf (g α)) idCR f)
                (idext (symCR ∘ renVal-reflect f ∘ `) (embNf (g α)))))
            (embNf A))
          (symCR (subst-eval (embNf A) (renCR f ∘ idCR) (embNf ∘ g)))))
      (symCR (renVal-eval (subst (embNf ∘ g) (embNf A)) idCR f))))
  (sym (ren-reify (idext idCR (subst (embNf ∘ g) (embNf A))) f))
\end{code}

Pushing a substitution through a renaming

\begin{code}
substNf-renNf : ∀{Φ Ψ Θ}
  → (g : Ren Φ Ψ)
  → (f : SubNf Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    --------------------------------------
  → substNf (f ∘ g) A ≡ substNf f (renNf g A)
substNf-renNf g f A = reifyCR
  (transCR
    (subst-eval (embNf A) idCR (embNf ∘ f ∘ g))
    (transCR
      (transCR
        (symCR (ren-eval (embNf A) (λ α → idext idCR (embNf (f α))) g))
        (symCR
          (evalCRSubst (λ α → idext idCR (embNf (f α))) (ren-embNf g A))))
      (symCR (subst-eval (embNf (renNf g A)) idCR (embNf ∘ f)))))
\end{code}

Pushing renaming through a one variable normal substitution

\begin{code}
ren[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          --------------------------------------------------------------
        → renNf ρ (t [ u ]Nf) ≡ (renNf (ext ρ) t [ renNf ρ u ]Nf)
ren[]Nf ρ t u = trans
  (sym (renNf-substNf (substNf-cons (ne ∘ `) u) ρ t))
  (trans
    (substNf-cong
      {f = renNf ρ ∘ substNf-cons (ne ∘ `) u}
      {g = substNf-cons (ne ∘ `) (renNf ρ u) ∘ ext ρ}
      (λ { Z → refl ; (S α) → refl})
      t)
    (substNf-renNf (ext ρ)(substNf-cons (ne ∘ `) (renNf ρ u)) t))
\end{code}

Pushing a normal substitution through a one place normal substitution

\begin{code}
subst[]Nf : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
    --------------------------------------------------------------
  → substNf ρ (B [ A ]Nf) ≡ (substNf (extsNf ρ) B [ substNf ρ A ]Nf)
subst[]Nf ρ A B = trans
  (sym (substNf-comp (substNf-cons (ne ∘ `) A) ρ B))
  (trans
    (substNf-cong
      {f = substNf ρ ∘ substNf-cons (ne ∘ `) A}
      {g = substNf (substNf-cons (ne ∘ `) (substNf ρ A)) ∘ extsNf ρ}
      (λ { Z     → sym (substNf-∋ (substNf-cons (ne ∘ `) (substNf ρ A)) Z) 
         ; (S α) → trans
              (trans (substNf-∋ ρ α) (sym (substNf-id (ρ α))))
              (substNf-renNf
                S
                (substNf-cons (ne ∘ `) (substNf ρ A))
                (ρ α))})
      B)
    (substNf-comp  (extsNf ρ) (substNf-cons (ne ∘ `) (substNf ρ A)) B))
\end{code}

Extending a normal environment and then embedding is the same as
embedding and then extending.

\begin{code}
substNf-lemma : ∀{Φ Ψ K J}
  (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (t : Φ ,⋆ K ⊢⋆ J)
  → subst (exts (embNf ∘ ρ)) t ≡ subst (embNf ∘ extsNf ρ) t
substNf-lemma ρ t =
  subst-cong (λ { Z → refl ; (S x) → sym (ren-embNf S (ρ x))}) t
\end{code}

Repair a mismatch between two different ways of extending an environment

\begin{code}
substNf-lemma' : ∀{Φ K J}
  → (B : Φ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B ((renVal S ∘ idEnv _) ,,⋆ fresh))
substNf-lemma' B = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S x) → symCR (renVal-reflect S (` x))}) B)
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
    ((reify (eval (subst (exts (embNf ∘ ρ)) (embNf B))
                 ((renVal S ∘ idEnv _) ,,⋆ fresh)))
    [ substNf ρ A ]Nf)
subst[]Nf' ρ A B =
  trans (subst[]Nf ρ A B)
  (substNf-cong' (substNf-cons (ne ∘ `) (substNf ρ A))
     {A = substNf (extsNf (λ {K = K₁} → ρ)) B}
     {A' =
      reify
      (eval (subst (exts (embNf ∘ ρ)) (embNf B))
       ((renVal S ∘ idEnv _) ,,⋆ fresh))}
     (trans (sym (completeness (≡2β (substNf-lemma ρ (embNf B)))))
              (substNf-lemma'  (subst (exts (embNf ∘ ρ)) (embNf B)))))
\end{code}

\begin{code}
weakenNf-renNf : ∀ {Φ Ψ}
  → (ρ⋆ : Ren Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (renNf ρ⋆ A) ≡ renNf (ext ρ⋆ {K = K}) (weakenNf A)
weakenNf-renNf ρ⋆ A = trans (sym (renNf-comp _)) (renNf-comp _)

weakenNf-substNf : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (substNf σ⋆ A) ≡ substNf (extsNf σ⋆ {K = K}) (weakenNf A)
weakenNf-substNf σ⋆ A = trans
  (sym (renNf-substNf σ⋆ S A))
  (substNf-renNf S (extsNf σ⋆) A)

weakenNf[] : ∀ {Φ K}(B : Φ ⊢Nf⋆ K)
        → (A : Φ ⊢Nf⋆ *)
        → A ≡ (weakenNf A [ B ]Nf)
weakenNf[] B A = trans
  (trans (sym (stability A))
         (evalCRSubst idCR (sym (subst-id (embNf A)))))
  (substNf-renNf S (substNf-cons (ne ∘ `) B) A)

open import Data.Sum

subst-nf-Π : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (B : Φ ,⋆ K ⊢Nf⋆ *)
  → substNf (extsNf σ⋆) B
    ≡
    eval (subst (exts (embNf ∘ σ⋆)) (embNf B)) (exte (idEnv Ψ))
subst-nf-Π σ⋆ B = trans
  (evalCRSubst idCR (sym (substNf-lemma σ⋆ (embNf B))))
  (substNf-lemma' (subst (exts (embNf ∘ σ⋆)) (embNf B)))

subst-nf-μ : ∀ {Φ Ψ}{K}
  → (σ⋆ : SubNf Φ Ψ)
  → (A  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (B  : Φ ⊢Nf⋆ K)
  → substNf σ⋆ (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
    ≡
    nf
    (embNf (substNf σ⋆ A) ·
     ƛ (μ (embNf (weakenNf (substNf σ⋆ A))) (` Z))
     · embNf (substNf σ⋆ B))
subst-nf-μ σ⋆ A B = trans
  (sym (substNf-nf σ⋆ (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)))
  (completeness
    {s = subst (embNf ∘ σ⋆) (embNf A) · ƛ (μ (subst (exts (embNf ∘ σ⋆)) (embNf (weakenNf A))) (` Z)) · subst (embNf ∘ σ⋆) (embNf B)}
    {(embNf (substNf σ⋆ A) · ƛ (μ (embNf (weakenNf (substNf σ⋆ A))) (` Z)) · embNf (substNf σ⋆ B))}
    (·≡β
      (·≡β
        (soundness (subst (embNf ∘ σ⋆) (embNf A)))
        (ƛ≡β (μ≡β
          (trans≡β
            (trans≡β
              (≡2β (cong (subst (exts (embNf ∘ σ⋆))) (ren-embNf S A)))
              (trans≡β
                (≡2β (sym (subst-ren (embNf A))))
                (trans≡β
                  (soundness (subst (weaken ∘ embNf ∘ σ⋆) (embNf A)))
                  (≡2β
                    (cong embNf {nf (subst (weaken ∘ embNf ∘ σ⋆) (embNf A))}{substNf (renNf S ∘ σ⋆) A}
                    (cong nf (subst-cong (sym ∘ ren-embNf S ∘ σ⋆) (embNf A))))))))
            (≡2β (cong embNf (renNf-substNf σ⋆ S A))))
          (refl≡β (` Z)))))
      (soundness (subst (embNf ∘ σ⋆) (embNf B)))))
\end{code}

\begin{code}
substNf-cons-[]Nf : ∀{Φ K Ψ'}{σ : SubNf Ψ' Φ}{A : Φ ⊢Nf⋆ K}(X : Ψ' ,⋆ K ⊢Nf⋆ *) → 
  substNf (substNf-cons σ A) X
  ≡
  reify (eval (subst (exts (embNf ∘ σ)) (embNf X)) (exte (idEnv Φ)))
  [ A ]Nf
substNf-cons-[]Nf {σ = σ}{A} X = trans
  (trans (substNf-cong {f = substNf-cons σ A}{g = substNf (substNf-cons (ne ∘ `) A) ∘ extsNf σ} (λ {Z → sym (stability A) ; (S α) → trans (trans (sym (stability (σ α))) (cong nf (sym (subst-id (embNf (σ α)))))) (substNf-renNf S (substNf-cons (ne ∘ `) A) (σ α)) }) X)
         (substNf-comp (extsNf σ)
                       (substNf-cons (ne ∘ `) A)
                       X))
  (cong (_[ A ]Nf)
        (subst-nf-Π σ X))
\end{code}
