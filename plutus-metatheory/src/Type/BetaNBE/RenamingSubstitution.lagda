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
subNf : ∀ {Φ Ψ}
  → SubNf Φ Ψ
    -------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
subNf ρ n = nf (sub (embNf ∘ ρ) (embNf n))
\end{code}

First monad law for subNf

\begin{code}
subNf-id : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → subNf (ne ∘ `) n ≡ n
subNf-id n = trans
  (reifyCR (fund idCR (≡2β (sub-id (embNf n)))))
  (stability n)
\end{code}

This version of the first monad law might be η compatible as it doesn't rely
on sub-id

\begin{code}
subNf-id' : ∀ {Φ J}
  → (n : Φ ⊢Nf⋆ J)
  → subNf (nf ∘ `) n ≡ n
subNf-id' n = trans
  (reifyCR
    (transCR
      (sub-eval (embNf n) idCR (embNf ∘ nf ∘ `))
      (idext
        (λ α → fund idCR (≡2β (cong embNf (stability (ne (` α))))))
        (embNf n))))
  (stability n)
\end{code}

Second monad law for subNf
This is often holds definitionally for substitution (e.g. sub) but not here.

\begin{code}
subNf-∋ : ∀ {Φ Ψ J}
  → (ρ : SubNf Φ Ψ)
  → (α : Φ ∋⋆ J)
  → subNf ρ (ne (` α)) ≡ ρ α
subNf-∋ ρ α = stability (ρ α) 
\end{code}



Two lemmas that aim to remove a superfluous additional normalisation
via stability

\begin{code}
subNf-nf : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
  → ∀ {J}
  → (t : Φ ⊢⋆ J)
    -------------------------------------------
  → nf (sub (embNf ∘ σ) t) ≡ subNf σ (nf t)
subNf-nf σ t = trans
  (reifyCR (sub-eval t idCR (embNf ∘ σ)))
  (trans
    (sym
      (reifyCR (fund (λ x → idext idCR (embNf (σ x))) (sym≡β (soundness t)))))
    (sym (reifyCR (sub-eval (embNf (nf t)) idCR (embNf ∘ σ)))))
\end{code}

Third Monad Law for subNf

\begin{code}
subNf-comp : ∀{Φ Ψ Θ}
  (g : SubNf Φ Ψ)
  (f : SubNf Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -----------------------------------------------
  → subNf (subNf f ∘ g) A ≡ subNf f (subNf g A)
subNf-comp g f A = trans
  (trans
    (trans
      (reifyCR
        (sub-eval
          (embNf A)
          idCR
          (embNf ∘ nf ∘ sub (embNf ∘ f) ∘ embNf ∘ g)))
      (trans (reifyCR
               (idext
                 (λ x → fund
                   idCR
                   (sym≡β (soundness (sub (embNf ∘ f) (embNf (g x))))))
                 (embNf A)))
             (sym
               (reifyCR
                 (sub-eval
                   (embNf A)
                   idCR
                   (sub (embNf ∘ f) ∘ embNf ∘ g))))))
    (completeness (≡2β (sub-comp (embNf A)))))
  (subNf-nf f (sub (embNf ∘ g) (embNf A)))
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
subNf-cons : ∀{Φ Ψ}
  → (∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{J}(A : Ψ ⊢Nf⋆ J)
  → (∀{K} → Φ ,⋆ J ∋⋆ K → Ψ ⊢Nf⋆ K)
subNf-cons σ A Z     = A
subNf-cons σ A (S x) = σ x
\end{code}

Substitution of one variable

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = subNf (subNf-cons (ne ∘ `) B) A
\end{code}

Congruence lemma for sub
\begin{code}
subNf-cong : ∀ {Φ Ψ}
  → {f g : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Nf⋆ K)
    -------------------------------
  → subNf f A ≡ subNf g A
subNf-cong p A =
 reifyCR (fund idCR (≡2β (sub-cong (cong embNf ∘ p ) (embNf A))))
\end{code}

\begin{code}
subNf-cong' : ∀ {Φ Ψ}
  → (f : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ∀{K}{A A' : Φ ⊢Nf⋆ K}
  → A ≡ A'
    -------------------------------
  → subNf f A ≡ subNf f A'
subNf-cong' f p = cong (subNf f) p
\end{code}

Pushing renaming through normal substitution

\begin{code}
renNf-subNf : ∀{Φ Ψ Θ}
  → (g : SubNf Φ Ψ)
  → (f : Ren Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
   -----------------------------------------------------
  → subNf (renNf f ∘ g) A ≡ renNf f (subNf g A)
renNf-subNf g f A = trans
  (reifyCR
    (transCR
      (transCR
        (sub-eval (embNf A) idCR (embNf ∘ renNf f ∘ g))
        (transCR
          (idext
            (λ α → transCR
              (evalCRSubst idCR (ren-embNf f (g α)))
              (transCR
                (ren-eval (embNf (g α)) idCR f)
                (idext (symCR ∘ renVal-reflect f ∘ `) (embNf (g α)))))
            (embNf A))
          (symCR (sub-eval (embNf A) (renCR f ∘ idCR) (embNf ∘ g)))))
      (symCR (renVal-eval (sub (embNf ∘ g) (embNf A)) idCR f))))
  (sym (ren-reify (idext idCR (sub (embNf ∘ g) (embNf A))) f))
\end{code}

Pushing a substitution through a renaming

\begin{code}
subNf-renNf : ∀{Φ Ψ Θ}
  → (g : Ren Φ Ψ)
  → (f : SubNf Ψ Θ)
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    --------------------------------------
  → subNf (f ∘ g) A ≡ subNf f (renNf g A)
subNf-renNf g f A = reifyCR
  (transCR
    (sub-eval (embNf A) idCR (embNf ∘ f ∘ g))
    (transCR
      (transCR
        (symCR (ren-eval (embNf A) (λ α → idext idCR (embNf (f α))) g))
        (symCR
          (evalCRSubst (λ α → idext idCR (embNf (f α))) (ren-embNf g A))))
      (symCR (sub-eval (embNf (renNf g A)) idCR (embNf ∘ f)))))
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
  (sym (renNf-subNf (subNf-cons (ne ∘ `) u) ρ t))
  (trans
    (subNf-cong
      {f = renNf ρ ∘ subNf-cons (ne ∘ `) u}
      {g = subNf-cons (ne ∘ `) (renNf ρ u) ∘ ext ρ}
      (λ { Z → refl ; (S α) → refl})
      t)
    (subNf-renNf (ext ρ)(subNf-cons (ne ∘ `) (renNf ρ u)) t))
\end{code}

Pushing a normal substitution through a one place normal substitution

\begin{code}
sub[]Nf : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
    --------------------------------------------------------------
  → subNf ρ (B [ A ]Nf) ≡ (subNf (extsNf ρ) B [ subNf ρ A ]Nf)
sub[]Nf ρ A B = trans
  (sym (subNf-comp (subNf-cons (ne ∘ `) A) ρ B))
  (trans
    (subNf-cong
      {f = subNf ρ ∘ subNf-cons (ne ∘ `) A}
      {g = subNf (subNf-cons (ne ∘ `) (subNf ρ A)) ∘ extsNf ρ}
      (λ { Z     → sym (subNf-∋ (subNf-cons (ne ∘ `) (subNf ρ A)) Z) 
         ; (S α) → trans
              (trans (subNf-∋ ρ α) (sym (subNf-id (ρ α))))
              (subNf-renNf
                S
                (subNf-cons (ne ∘ `) (subNf ρ A))
                (ρ α))})
      B)
    (subNf-comp  (extsNf ρ) (subNf-cons (ne ∘ `) (subNf ρ A)) B))
\end{code}

Extending a normal environment and then embedding is the same as
embedding and then extending.

\begin{code}
subNf-lemma : ∀{Φ Ψ K J}
  (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (t : Φ ,⋆ K ⊢⋆ J)
  → sub (exts (embNf ∘ ρ)) t ≡ sub (embNf ∘ extsNf ρ) t
subNf-lemma ρ t =
  sub-cong (λ { Z → refl ; (S x) → sym (ren-embNf S (ρ x))}) t
\end{code}

Repair a mismatch between two different ways of extending an environment

\begin{code}
subNf-lemma' : ∀{Φ K J}
  → (B : Φ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B ((renVal S ∘ idEnv _) ,,⋆ fresh))
subNf-lemma' B = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S x) → symCR (renVal-reflect S (` x))}) B)
\end{code}

combining the above lemmas

note: there are several mismatches here, one due to two different ways
of extending a normal substitution and another due to two different
ways of extending an environment

\begin{code}
sub[]Nf' : ∀{Φ Ψ K J}
  → (ρ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → (A : Φ ⊢Nf⋆ K)
  → (B : Φ ,⋆ K ⊢Nf⋆ J)
  → subNf ρ (B [ A ]Nf)
    ≡
    ((reify (eval (sub (exts (embNf ∘ ρ)) (embNf B))
                 ((renVal S ∘ idEnv _) ,,⋆ fresh)))
    [ subNf ρ A ]Nf)
sub[]Nf' ρ A B =
  trans (sub[]Nf ρ A B)
  (subNf-cong' (subNf-cons (ne ∘ `) (subNf ρ A))
     {A = subNf (extsNf ρ) B}
     {A' =
      reify
      (eval (sub (exts (embNf ∘ ρ)) (embNf B))
       ((renVal S ∘ idEnv _) ,,⋆ fresh))}
     (trans (sym (completeness (≡2β (subNf-lemma ρ (embNf B)))))
              (subNf-lemma'  (sub (exts (embNf ∘ ρ)) (embNf B)))))
\end{code}

\begin{code}
weakenNf-renNf : ∀ {Φ Ψ}
  → (ρ⋆ : Ren Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (renNf ρ⋆ A) ≡ renNf (ext ρ⋆ {K = K}) (weakenNf A)
weakenNf-renNf ρ⋆ A = trans (sym (renNf-comp _)) (renNf-comp _)

weakenNf-subNf : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (subNf σ⋆ A) ≡ subNf (extsNf σ⋆ {K = K}) (weakenNf A)
weakenNf-subNf σ⋆ A = trans
  (sym (renNf-subNf σ⋆ S A))
  (subNf-renNf S (extsNf σ⋆) A)

weakenNf[] : ∀ {Φ K}(B : Φ ⊢Nf⋆ K)
        → (A : Φ ⊢Nf⋆ *)
        → A ≡ (weakenNf A [ B ]Nf)
weakenNf[] B A = trans
  (trans (sym (stability A))
         (evalCRSubst idCR (sym (sub-id (embNf A)))))
  (subNf-renNf S (subNf-cons (ne ∘ `) B) A)

open import Data.Sum

sub-nf-Π : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → ∀{K}
  → (B : Φ ,⋆ K ⊢Nf⋆ *)
  → subNf (extsNf σ⋆) B
    ≡
    eval (sub (exts (embNf ∘ σ⋆)) (embNf B)) (exte (idEnv Ψ))
sub-nf-Π σ⋆ B = trans
  (evalCRSubst idCR (sym (subNf-lemma σ⋆ (embNf B))))
  (subNf-lemma' (sub (exts (embNf ∘ σ⋆)) (embNf B)))

sub-nf-μ : ∀ {Φ Ψ}{K}
  → (σ⋆ : SubNf Φ Ψ)
  → (A  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (B  : Φ ⊢Nf⋆ K)
  → subNf σ⋆ (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
    ≡
    nf
    (embNf (subNf σ⋆ A) ·
     ƛ (μ (embNf (weakenNf (subNf σ⋆ A))) (` Z))
     · embNf (subNf σ⋆ B))
sub-nf-μ σ⋆ A B = trans
  (sym (subNf-nf σ⋆ (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)))
  (completeness
    {s = sub (embNf ∘ σ⋆) (embNf A) · ƛ (μ (sub (exts (embNf ∘ σ⋆)) (embNf (weakenNf A))) (` Z)) · sub (embNf ∘ σ⋆) (embNf B)}
    {(embNf (subNf σ⋆ A) · ƛ (μ (embNf (weakenNf (subNf σ⋆ A))) (` Z)) · embNf (subNf σ⋆ B))}
    (·≡β
      (·≡β
        (soundness (sub (embNf ∘ σ⋆) (embNf A)))
        (ƛ≡β (μ≡β
          (trans≡β
            (trans≡β
              (≡2β (cong (sub (exts (embNf ∘ σ⋆))) (ren-embNf S A)))
              (trans≡β
                (≡2β (sym (sub-ren (embNf A))))
                (trans≡β
                  (soundness (sub (weaken ∘ embNf ∘ σ⋆) (embNf A)))
                  (≡2β
                    (cong embNf {nf (sub (weaken ∘ embNf ∘ σ⋆) (embNf A))}{subNf (renNf S ∘ σ⋆) A}
                    (cong nf (sub-cong (sym ∘ ren-embNf S ∘ σ⋆) (embNf A))))))))
            (≡2β (cong embNf (renNf-subNf σ⋆ S A))))
          (refl≡β (` Z)))))
      (soundness (sub (embNf ∘ σ⋆) (embNf B)))))
\end{code}

\begin{code}
subNf-cons-[]Nf : ∀{Φ K Ψ'}{σ : SubNf Ψ' Φ}{A : Φ ⊢Nf⋆ K}(X : Ψ' ,⋆ K ⊢Nf⋆ *) → 
  subNf (subNf-cons σ A) X
  ≡
  reify (eval (sub (exts (embNf ∘ σ)) (embNf X)) (exte (idEnv Φ))) [ A ]Nf
subNf-cons-[]Nf {σ = σ}{A} X = trans
  (trans (subNf-cong {f = subNf-cons σ A}{g = subNf (subNf-cons (ne ∘ `) A) ∘ extsNf σ} (λ {Z → sym (stability A) ; (S α) → trans (trans (sym (stability (σ α))) (cong nf (sym (sub-id (embNf (σ α)))))) (subNf-renNf S (subNf-cons (ne ∘ `) A) (σ α)) }) X)
         (subNf-comp (extsNf σ)
                       (subNf-cons (ne ∘ `) A)
                       X))
  (cong (_[ A ]Nf)
        (sub-nf-Π σ X))
\end{code}
