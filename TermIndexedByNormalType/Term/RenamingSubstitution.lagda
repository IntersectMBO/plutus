\begin{code}
module TermIndexedByNormalType.Term.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq; [_] to [_]≅)
open import Data.Sum

open import Type
open import Type.Equality
import Type.RenamingSubstitution as ⋆
--open import Type.Reduction
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import TermIndexedByNormalType.Term
\end{code}


## Renaming

\begin{code}
ext : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K } {A : ∥ Γ ∥ ⊢Nf⋆ J} {B : ∥ Γ ∥ ⊢Nf⋆ K}
     → Γ , B ∋ A
       -------------------------------
     → Δ , renameNf ρ⋆ B ∋ renameNf ρ⋆ A)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}

ext⋆ : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ∋⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢Nf⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ∋ renameNf (⋆.ext ρ⋆) A )
ext⋆ {Γ}{Δ} ρ⋆ ρ {J}{K}{A} (T x) =
  substEq (λ A → Δ ,⋆ K ∋ A)
          (trans (sym (renameNf-comp _)) (renameNf-comp _))
          (T (ρ x))
\end{code}

\begin{code}
renameE : ∀{Γ Δ K K'} → ⋆.Ren Γ Δ → EvalCxt Γ K K' → EvalCxt Δ K K'
renameE ρ •        = •
renameE ρ (E ·E t) = renameE ρ E ·E renameNf ρ t

renameE[] : ∀{Γ Δ K K'}(ρ : ⋆.Ren Γ Δ)(E : EvalCxt Γ K K')(t : Γ ⊢Nf⋆ K)
  → renameNf ρ (E [ t ]E) ≡ renameE ρ E [ renameNf ρ t ]E
renameE[] ρ •        t = refl
renameE[] ρ (E ·E u) t =
  trans (rename-reify (AppCR (idext idCR (embNf (E [ t ]E)))
                                 (idext idCR (embNf u)))
                         ρ)
        (trans (reifyCR (renameVal-eval (embNf (E [ t ]E) · embNf u) idCR ρ))
                        (trans (trans (reifyCR (transCR (AppCR (idext (renameVal-reflect ρ ∘ `) (embNf (E [ t ]E))) (idext (renameVal-reflect ρ ∘ `) (embNf u))) (symCR (rename-eval (embNf (E [ t ]E) · embNf u) idCR ρ))))
                             (sym (cong₂ (λ f a → nf (f · a))
                                         (rename-embNf ρ (E [ t ]E))
                                         (rename-embNf ρ u))) )
                      (cong (λ f → nf (embNf f · embNf (renameNf ρ u)))
                            (renameE[] ρ E t)) ))
\end{code}

\begin{code}
rename-nf : ∀{Γ Δ K}
  → (A : ∥ Γ ∥ ⊢⋆ K)
  → (ρ⋆ : ∀ {J} → ∥ Γ ∥ ∋⋆ J → ∥ Δ ∥ ∋⋆ J)
  → renameNf ρ⋆ (nf A) ≡ nf (⋆.rename ρ⋆ A)
rename-nf A ρ⋆ = trans
  (rename-reify (idext idCR A) ρ⋆)
  (reifyCR
    (transCR
      (transCR
        (renameVal-eval A idCR ρ⋆)
        (idext (λ α → renameVal-reflect ρ⋆ (` α)) A))
      (symCR (rename-eval A idCR ρ⋆))))
\end{code}

\begin{code}

rename : ∀ {Γ Δ}
  → (ρ⋆ : ∀ {J} → ∥ Γ ∥ ∋⋆ J → ∥ Δ ∥ ∋⋆ J)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
    ------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Δ ⊢ renameNf ρ⋆ A )
rename ρ⋆ ρ (` x)    = ` (ρ x)
rename ρ⋆ ρ (ƛ N)    = ƛ (rename ρ⋆ (ext ρ⋆ ρ) N)
rename ρ⋆ ρ (L · M)  = rename ρ⋆ ρ L · rename ρ⋆ ρ M 
rename ρ⋆ ρ (Λ N)    = Λ (rename (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N)
rename {Γ}{Δ} ρ⋆ ρ (_·⋆_ {B = B} t A) =
  substEq (Δ ⊢_)
          (sym (rename[]Nf ρ⋆ B A))
          (rename ρ⋆ ρ t ·⋆ renameNf ρ⋆ A)
rename {Γ}{Δ} ρ⋆ ρ (wrap B E M p) =
  wrap (renameNf (⋆.ext ρ⋆) B)
       (renameE ρ⋆ E)
       (substEq (Δ ⊢_)
                (trans (renameE[] ρ⋆ E (B [ ne (μ B) ]Nf))
                       (cong (renameE ρ⋆ E [_]E)
                             (rename[]Nf ρ⋆ B (ne (μ B)))))
                (rename ρ⋆ ρ M))
       (trans (cong (renameNf ρ⋆) p) (renameE[] ρ⋆ E (ne (μ B))))
rename {Γ}{Δ} ρ⋆ ρ (unwrap {S = B} E p M) = substEq
  (Δ ⊢_)
  (trans (cong (renameE ρ⋆ E [_]E) (sym (rename[]Nf ρ⋆ B (ne (μ B)))))
         (sym (renameE[] ρ⋆ E (B [ ne (μ B) ]Nf))))
  (unwrap (renameE ρ⋆ E)
          (trans (cong (renameNf ρ⋆) p) (renameE[] ρ⋆ E (ne (μ B))))
          (rename ρ⋆ ρ M))
rename {Γ}{Δ} ρ⋆ ρ (wrap1 pat arg term) = wrap1
  (renameNf ρ⋆ pat)
  (renameNf ρ⋆ arg)
  (substEq
    (Δ ⊢_)
    (trans
      (rename-nf {Γ}{Δ} (embNf pat · (μ1 · embNf pat) · embNf arg) ρ⋆)
      (cong₂ (λ (p : ∥ Δ ∥ ⊢⋆ _)(a : ∥ Δ ∥ ⊢⋆ _) → nf (p · (μ1 · p) · a))
             (sym (rename-embNf ρ⋆ pat))
             (sym (rename-embNf ρ⋆ arg))))
    (rename ρ⋆ ρ term))
rename {Γ}{Δ} ρ⋆ ρ (unwrap1 {pat = pat}{arg} term) = substEq
  (Δ ⊢_)
  (trans  -- same as above but backwards
    (cong₂ (λ (p : ∥ Δ ∥ ⊢⋆ _)(a : ∥ Δ ∥ ⊢⋆ _) → nf (p · (μ1 · p) · a))
             (rename-embNf ρ⋆ pat)
             (rename-embNf ρ⋆ arg))
    (sym (rename-nf {Γ}{Δ} (embNf pat · (μ1 · embNf pat) · embNf arg) ρ⋆)))
  (unwrap1 (rename ρ⋆ ρ term))
\end{code}

\begin{code}
weaken : ∀ {Φ J}{A : ∥ Φ ∥ ⊢Nf⋆ J}{K}{B : ∥ Φ ∥ ⊢Nf⋆ K}
  → Φ ⊢ A
    -------------
  → Φ , B ⊢ A
weaken {Φ}{J}{A}{K}{B} x = 
  substEq (λ x → Φ , B ⊢ x)
          (renameNf-id A)
          (rename id
                  (λ x → substEq (λ A → Φ , B ∋ A) (sym (renameNf-id _)) (S x))
                  x)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ J}{A : ∥ Φ ∥ ⊢Nf⋆ J}{K}
  → Φ ⊢ A
    ------------------
  → Φ ,⋆ K ⊢ weakenNf A
weaken⋆ x = rename _∋⋆_.S _∋_.T x
\end{code}

## Substitution

\begin{code}
exts : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢Nf⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ⊢ substNf σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {K} {A : ∥ Γ ∥ ⊢Nf⋆ J} {B : ∥ Γ ∥ ⊢Nf⋆ K}
     → Γ , B ∋ A
     -------------------------------
     → Δ , substNf σ⋆ B ⊢ substNf σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢Nf⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ⊢ substNf σ⋆ A)
    ---------------------------------------------------
  → (∀ {J K}{A : ∥ Γ ,⋆ K ∥ ⊢Nf⋆ J}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ substNf (extsNf σ⋆) A )
exts⋆ {Γ}{Δ} σ⋆ σ {J}{K}(T {A = A} x) = 
  substEq (λ x → Δ ,⋆ K ⊢ x)
          (trans (rename-reify (idext idCR (⋆.subst (embNf ∘ σ⋆) (embNf A))) S) (reifyCR (transCR (renameVal-eval (⋆.subst (embNf ∘ σ⋆) (embNf A)) idCR S)
                                                                                                (transCR (transCR (subst-eval  (embNf A) (renCR S ∘ idCR) (embNf ∘ σ⋆)) (transCR (idext (λ {x → transCR (transCR (idext (λ x → renameVal-reflect S (` x)) (embNf (σ⋆ x))) (symCR (rename-eval (embNf (σ⋆ x)) idCR S))) (symCR (evalCRSubst idCR (rename-embNf S (σ⋆ x))))}) (embNf A)) (symCR (subst-eval (embNf A) idCR (embNf ∘ renameNf S ∘ σ⋆))))) (evalCRSubst idCR (trans (⋆.subst-rename (embNf A)) (cong (λ x → ⋆.subst (embNf ∘ extsNf σ⋆) x) (sym (rename-embNf S A)))))))))
          (weaken⋆ (σ x))
\end{code}

\begin{code}
substE : ∀{Γ Δ K K'}
 → (σ⋆ : ∀ {K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
 → EvalCxt Γ K K'
 → EvalCxt Δ K K'
substE ρ •        = •
substE ρ (E ·E t) = substE ρ E ·E substNf ρ t

-- this is a bad name it should be substNf-substE or something
substE[] : ∀{Γ Δ K K'}
  → (σ : ∀ {K} → Γ ∋⋆ K → Δ ⊢Nf⋆ K)
  → (E : EvalCxt Γ K K')
  → (t : Γ ⊢Nf⋆ K)
  → substNf σ (E [ t ]E) ≡ substE σ E [ substNf σ t ]E
substE[] σ • t = refl
substE[] σ (E ·E u) t =
  trans (trans (reifyCR (subst-eval (embNf (nf (embNf (E [ t ]E) · embNf u))) idCR (embNf ∘ σ))) (trans (trans (sym (reifyCR (fund (λ x → idext idCR (embNf  (σ x))) (soundness (embNf (E [ t ]E) · embNf u))))) (sym (reifyCR (AppCR (subst-eval (embNf (E [ t ]E)) idCR (embNf ∘ σ)) (subst-eval (embNf u) idCR (embNf ∘ σ)))))) (reifyCR (AppCR (fund idCR (soundness (⋆.subst (embNf ∘ σ) (embNf (E [ t ]E))))) (fund idCR (soundness (⋆.subst (embNf ∘ σ) (embNf u))))))  )
  )
        (cong (λ f → nf (embNf f · embNf (substNf σ u))) (substE[] σ E t)) 
\end{code}

\begin{code}
subst : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢Nf⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ⊢ substNf σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Δ ⊢ substNf σ⋆ A)
subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ N)                     = ƛ (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst {Γ}{Δ} σ⋆ σ {J} (Λ {K = K}{B = B} N)                     =
  Λ (substEq (λ A → Δ ,⋆ K ⊢ A)
             (trans (sym (evalCRSubst idCR (substNf-lemma σ⋆ (embNf B))))
                    (substNf-lemma' (⋆.subst (⋆.exts (embNf ∘ σ⋆)) (embNf B))))
             (subst (extsNf σ⋆) (exts⋆ σ⋆ σ) N))
subst {Γ}{Δ} σ⋆ σ {J} (_·⋆_ {K = K}{B = B} L M) =
  substEq (λ A → Δ ⊢ A)
          (trans refl
                 (sym (subst[]Nf' σ⋆ M B)) )
          (subst σ⋆ σ L ·⋆ substNf σ⋆ M)
subst {Γ}{Δ} σ⋆ σ (wrap B E N p) =
  wrap
    (substNf (extsNf σ⋆) B)
    (substE σ⋆ E)
    (substEq (Δ ⊢_)
             (trans (substE[] σ⋆ E (B [ ne (μ B) ]Nf))
                    (cong (substE σ⋆ E [_]E)
                          (trans (subst[]Nf σ⋆ (ne (μ B)) B)
                                 (cong (substNf (extsNf σ⋆) B [_]Nf)
                                       (trans (reify-reflect _)
                                              (cong (ne ∘ μ) (reifyCR (transCR (transCR (subst-eval (embNf B) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.exts (embNf ∘ σ⋆))) (idext (λ{ Z → reflectCR refl ; (S x) → transCR (idext (λ { Z → reflectCR refl ; (S x) → renameVal-reflect S (` x)}) (⋆.rename S (embNf (σ⋆ x)))) (symCR (evalCRSubst idCR (rename-embNf S (σ⋆ x))))}) (embNf B))) (symCR (subst-eval (embNf B) idCR (embNf ∘ extsNf σ⋆)))))))))))
             (subst σ⋆ σ N))
    (trans (cong (substNf σ⋆) p)
           (trans (substE[] σ⋆ E (ne (μ B))) (cong (substE σ⋆ E [_]E)
                  (trans (reify-reflect _)
                         (cong (ne ∘ μ)
                               (reifyCR (transCR (transCR (subst-eval (embNf B) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.exts (embNf ∘ σ⋆))) (idext (λ { Z → reflectCR refl ; (S x) → transCR (idext (λ { Z → reflectCR refl ; (S x) → renameVal-reflect S (` x)}) (⋆.rename S (embNf (σ⋆ x)))) (symCR (evalCRSubst idCR (rename-embNf S (σ⋆ x))))} ) (embNf B))) (symCR (subst-eval (embNf B) idCR (embNf ∘ extsNf σ⋆))))))))))
subst {Γ}{Δ} σ⋆ σ (unwrap {S = A} E p M) =
  substEq (Δ ⊢_)
          (trans (cong (substE σ⋆ E [_]E)
                       (trans (reifyCR (transCR (transCR (subst-eval (embNf (substNf (extsNf σ⋆) A)) idCR (embNf ∘ (substNf-cons (ne ∘ `) (ne (μ (nf (⋆.subst (embNf ∘ extsNf σ⋆) (embNf A)))))))) (idext (λ { Z → transCR (reflectCR (cong μ (reifyCR (transCR (fund (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (sym≡β (soundness (⋆.subst (embNf ∘ extsNf σ⋆) (embNf A))))) (transCR (transCR (subst-eval (embNf A) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (embNf ∘ extsNf σ⋆)) (transCR (transCR (idext (λ{ Z → reflectCR refl ; (S x) → transCR (evalCRSubst (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (rename-embNf S (σ⋆ x))) (transCR (transCR (rename-eval (embNf (σ⋆ x)) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) S) (transCR (idext (renCR S ∘ idCR ) (embNf (σ⋆ x))) (symCR (subst-eval (embNf (σ⋆ x)) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (_⊢⋆_.` ∘ S))))) (evalCRSubst (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.subst-rename (embNf (σ⋆ x)))))}) (embNf A)) (symCR (subst-eval (embNf A) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.subst (⋆.subst-cons (_⊢⋆_.` ∘ S) (` Z)) ∘ ⋆.exts (embNf ∘ σ⋆))))) (evalCRSubst (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.subst-comp (embNf A))))) (fund (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (reifySR (evalSR (⋆.subst (⋆.exts (embNf ∘ σ⋆)) (embNf A)) (SR,,⋆ (renSR S ∘ idSR) (reflectSR (refl≡β _)))))) ))))) (symCR (evalCRSubst idCR (cong embNf (reify-reflect _)))) ; (S x) → reflectCR refl}) (embNf (substNf (extsNf σ⋆) A)))) (symCR (subst-eval (embNf (substNf (extsNf σ⋆) A)) idCR (embNf ∘ (substNf-cons (ne ∘ `) (substNf σ⋆ (ne (μ A)))))))))
                              (sym (subst[]Nf σ⋆ (ne (μ A)) A))))
                 (sym (substE[] σ⋆ E (A [ ne (μ A) ]Nf))))
          (unwrap (substE σ⋆ E)
                  (trans (cong (substNf σ⋆) p)
                         (trans (substE[] σ⋆ E (ne (μ A)))
                                (cong (substE σ⋆ E [_]E) (trans (reify-reflect _)
                         (cong (ne ∘ μ)
                               (reifyCR (transCR (transCR (subst-eval (embNf A) (CR,,⋆ (renCR S ∘ idCR) (reflectCR refl)) (⋆.exts (embNf ∘ σ⋆))) (idext (λ { Z → reflectCR refl ; (S x) → transCR (idext (λ { Z → reflectCR refl ; (S x) → renameVal-reflect S (` x)}) (⋆.rename S (embNf (σ⋆ x)))) (symCR (evalCRSubst idCR (rename-embNf S (σ⋆ x))))} ) (embNf A))) (symCR (subst-eval (embNf A) idCR (embNf ∘ extsNf σ⋆))))))))))
                  (subst σ⋆ σ M))

subst {Γ}{Δ} σ⋆ σ (wrap1 {K = K} pat arg term) = wrap1
  (substNf σ⋆ pat)
  (substNf σ⋆ arg)
  (substEq
    (Δ ⊢_)
    (trans
       (sym (substNf-nf σ⋆ (embNf pat · (μ1 · embNf pat) · embNf arg)))
       (AppCR
         (AppCR
           (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat))))
           (cong
             ne
             (cong
               (μ1 ·_)
               (completeness (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat)))))))
         (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf arg))))))
    (subst σ⋆ σ term))
subst {Γ}{Δ} σ⋆ σ (unwrap1 {pat = pat}{arg} term)       = substEq
  (Δ ⊢_)
  (sym  -- the same but backwards
    (trans
       (sym (substNf-nf σ⋆ (embNf pat · (μ1 · embNf pat) · embNf arg)))
       (AppCR
         (AppCR
           (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat))))
           (cong
             ne
             (cong
               (μ1 ·_)
               (completeness (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat)))))))
         (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf arg)))))))
  (unwrap1 (subst σ⋆ σ term))
\end{code}

\begin{code}
substcons : ∀{Γ Δ} →
  (σ⋆ : ∀{K} → ∥ Γ ∥  ∋⋆ K → ∥ Δ ∥ ⊢Nf⋆ K)
  → (∀ {J}{A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ⊢ substNf σ⋆ A)
  → ∀{J}{A : ∥ Γ ∥ ⊢Nf⋆ J}
  → (t : Δ ⊢ substNf σ⋆ A)
    ---------------------
  → (∀ {J} {B : ∥ Γ ∥ ⊢Nf⋆ J} → Γ , A ∋ B → Δ ⊢ substNf σ⋆ B)
substcons σ⋆ σ t Z     = t
substcons σ⋆ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀ {J Γ} {A B : ∥ Γ ∥ ⊢Nf⋆ J}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {J}{Γ}{A}{B} b a =
  substEq (λ A → Γ ⊢ A)
          (substNf-id A)
          (subst  (ne ∘ `)
                  (substcons (ne ∘ `)
                             (λ x → substEq (λ A → Γ ⊢ A)
                                            (sym (substNf-id _))
                                            (` x))
                             (substEq (λ A → Γ ⊢ A) (sym (substNf-id B)) a))
                  b)
\end{code}

\begin{code}
_[_]⋆ : ∀ {J Γ K} {B : ∥ Γ ,⋆ K ∥ ⊢Nf⋆ J}
        → Γ ,⋆ K ⊢ B
        → (A : ∥ Γ ∥ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
_[_]⋆ {J}{Γ}{K}{B} b A =
          subst (substNf-cons (ne ∘ `) A)
                 ( (λ {(T {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (trans (trans (sym (stability A')) (sym (reifyCR (rename-eval (embNf A') (λ x → idext idCR (embNf (substNf-cons (ne ∘ `) A x))) S)))) (sym (reifyCR (evalCRSubst (λ x → idext idCR (embNf (substNf-cons (ne ∘ `) A x))) (rename-embNf S A'))))) (reifyCR (symCR (subst-eval (embNf (renameNf S A')) idCR (embNf ∘ (substNf-cons (ne ∘ `) A))))))
                                     (` x)}))
                 b
\end{code}
