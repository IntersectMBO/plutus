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
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
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
renameTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    -----------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (renameNf ρ⋆ A ))
renameTermCon ρ⋆ (integer s i p)    = integer s i p
renameTermCon ρ⋆ (bytestring s b p) = bytestring s b p
renameTermCon ρ⋆ (size s)           = size s
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
rename ρ⋆ ρ (con c) = con (renameTermCon ρ⋆ c)
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
substTermCon : ∀ {Φ Ψ}
  → (σ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢Nf⋆ J)
    ------------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (substNf σ⋆ A ))
substTermCon σ⋆ (integer s i p)    = integer s i p
substTermCon σ⋆ (bytestring s b p) = bytestring s b p
substTermCon σ⋆ (size s)           = size s
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
subst σ⋆ σ (con c) = con (substTermCon σ⋆ c)
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
