\begin{code}
module Algorithmic.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq; [_] to [_]≅)
open import Data.Sum
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to _,,_)

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
open import Algorithmic
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
\end{code}

## Renaming

\begin{code}
Ren : ∀{Φ Ψ} → ⋆.Ren Φ Ψ → Ctx Φ → Ctx Ψ → Set
Ren ρ⋆ Γ Δ = (∀ {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ∋ renNf ρ⋆ A)

ext : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    --------------------------------------------------------------
  → {A : Φ ⊢Nf⋆ *} → Γ , B ∋ A → Δ , renNf ρ⋆ B ∋ renNf ρ⋆ A
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
weaken-ren : ∀ {Φ Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf (renNf ρ⋆ A) ≡ renNf (⋆.ext ρ⋆ {K = K}) (weakenNf A)
weaken-ren ρ⋆ A = trans (sym (renNf-comp _)) (renNf-comp _)

ext⋆ : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → ∀ {K}
    ---------------------------------------------------
  → {A : Φ ,⋆ K ⊢Nf⋆ *} → Γ ,⋆ K ∋ A → Δ ,⋆ K ∋ renNf (⋆.ext ρ⋆) A
ext⋆ ρ⋆ ρ (T x) = conv∋ (weaken-ren ρ⋆ _) (T (ρ x))
\end{code}

\begin{code}
renTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
    -----------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (renNf ρ⋆ A ))
renTermCon ρ⋆ (integer i)    = integer i
renTermCon ρ⋆ (bytestring b) = bytestring b
\end{code}

\begin{code}

ren : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
    ------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ renNf ρ⋆ A )

renTel : ∀ {Φ Φ' Γ Γ' Δ}
 → (ρ⋆ : ⋆.Ren Φ Φ')
 → (ρ : Ren ρ⋆ Γ Γ')
 → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
 → {As : List (Δ ⊢Nf⋆ *)}
 → Tel Γ Δ σ As
 → Tel Γ' Δ (renNf ρ⋆ ∘ σ) As

ren-nf-μ1 : ∀ {Φ Ψ}{K}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (pat  : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
  → (arg  : Φ ⊢Nf⋆ K)
  → renNf ρ⋆ (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
    ≡
    nf (embNf (renNf ρ⋆ pat)
        · (μ1 · embNf (renNf ρ⋆ pat))
        · embNf (renNf ρ⋆ arg))
ren-nf-μ1 ρ⋆ pat arg = trans
  (ren-nf ρ⋆ (embNf pat · (μ1 · embNf pat) · embNf arg))
  (cong₂ (λ (p : _ ⊢⋆ _)(a : _ ⊢⋆ _) → nf (p · (μ1 · p) · a))
         (sym (ren-embNf ρ⋆ pat))
         (sym (ren-embNf ρ⋆ arg)))

ren ρ⋆ ρ (` x)    = ` (ρ x)
ren ρ⋆ ρ (ƛ x N)    = ƛ x (ren ρ⋆ (ext ρ⋆ ρ) N)
ren ρ⋆ ρ (L · M)  = ren ρ⋆ ρ L · ren ρ⋆ ρ M 
ren ρ⋆ ρ (Λ x N)    = Λ x (ren (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N)
ren ρ⋆ ρ (_·⋆_ {B = B} t A) =
  conv⊢ (sym (ren[]Nf ρ⋆ B A)) (ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A)
ren ρ⋆ ρ (wrap1 pat arg term) = wrap1
  (renNf ρ⋆ pat)
  (renNf ρ⋆ arg)
  (conv⊢ (ren-nf-μ1 ρ⋆ pat arg) (ren ρ⋆ ρ term))
ren ρ⋆ ρ (unwrap1 {pat = pat}{arg} term) =
  conv⊢ (sym (ren-nf-μ1 ρ⋆ pat arg)) (unwrap1 (ren ρ⋆ ρ term))
ren ρ⋆ ρ (con c) = con (renTermCon ρ⋆ c)
ren ρ⋆ ρ (builtin bn σ X) =
  let _ ,, _ ,, A = SIG bn in conv⊢
  (renNf-substNf σ ρ⋆ A)
  (builtin bn (renNf ρ⋆ ∘ σ) (renTel ρ⋆ ρ X))
ren ρ⋆ ρ (error A) = error (renNf ρ⋆ A)

renTel ρ⋆ ρ     {As = []}     _         = _
renTel ρ⋆ ρ {σ} {As = A ∷ As} (M ,, Ms) =
  conv⊢ (sym (renNf-substNf σ ρ⋆ A)) (ren ρ⋆ ρ M) ,, renTel ρ⋆ ρ Ms
\end{code}

\begin{code}
weaken : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weaken x = 
  conv⊢ (renNf-id _) (ren id (conv∋ (sym (renNf-id _)) ∘ S) x)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K}
  → Γ ⊢ A
    ------------------
  → Γ ,⋆ K ⊢ weakenNf A
weaken⋆ x = ren _∋⋆_.S _∋_.T x
\end{code}

## Substitution

\begin{code}
Sub : ∀{Φ Ψ} → SubNf Φ Ψ → Ctx Φ → Ctx Ψ → Set
Sub σ⋆ Γ Δ = (∀ {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ⊢ substNf σ⋆ A)

exts : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    ---------------------------------------------------
  → (∀ {A : Φ ⊢Nf⋆ *}
     → Γ , B ∋ A
     -------------------------------
     → Δ , substNf σ⋆ B ⊢ substNf σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
    ---------------------------------------------------
  → (∀ {K}{A : Φ ,⋆ K ⊢Nf⋆ *}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ substNf (extsNf σ⋆) A )
exts⋆ {Φ}{Ψ}{Γ}{Δ} σ⋆ σ {K}(T {A = A} x) = 
  substEq (λ x → Δ ,⋆ K ⊢ x)
          (trans (ren-reify (idext idCR (⋆.subst (embNf ∘ σ⋆) (embNf A))) S) (reifyCR (transCR {K = *} (renVal-eval (⋆.subst (embNf ∘ σ⋆) (embNf A)) idCR S)
                                                                                                (transCR {K = *} (transCR {K = *} (subst-eval  (embNf A) (renCR S ∘ idCR) (embNf ∘ σ⋆)) (transCR {K = *} (idext (λ {x → transCR (transCR (idext (λ x → renVal-reflect S (` x)) (embNf (σ⋆ x))) (symCR (ren-eval (embNf (σ⋆ x)) idCR S))) (symCR (evalCRSubst idCR (ren-embNf S (σ⋆ x))))}) (embNf A)) (symCR {K = *} (subst-eval (embNf A) idCR (embNf ∘ renNf S ∘ σ⋆))))) (evalCRSubst idCR (trans (⋆.subst-ren (embNf A)) (cong (λ x → ⋆.subst (embNf ∘ extsNf σ⋆) x) (sym (ren-embNf S A)))))))))
          (weaken⋆ (σ x))
\end{code}

\begin{code}
substTermCon : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
    ------------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (substNf σ⋆ A ))
substTermCon σ⋆ (integer i)    = integer i
substTermCon σ⋆ (bytestring b) = bytestring b
\end{code}

\begin{code}
substTel : ∀ {Φ Φ' Γ Γ' Δ}
 → (σ⋆ : SubNf Φ Φ')
 → (σ : Sub σ⋆ Γ Γ')
 → {σ' : SubNf Δ Φ}
 → {As : List (Δ ⊢Nf⋆ *)}
 → Tel Γ Δ σ' As
 → Tel Γ' Δ (substNf σ⋆ ∘ σ') As

subst : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
    ---------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ substNf σ⋆ A)

substTel σ⋆ σ {As = []}     _         = _
substTel {Φ}{Φ'}{Γ}{Γ'} σ⋆ σ {σ'} {As = A ∷ As} (M ,, Ms) =
  substEq (Γ' ⊢_) (sym (substNf-comp σ' σ⋆ A)) (subst σ⋆ σ M)
  ,,
  substTel σ⋆ σ Ms

subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ x N)                     = ƛ x (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst {Φ}{Ψ}{Γ}{Δ} σ⋆ σ {J} (Λ {K = K} x {B = B} N)                     =
  Λ x (substEq (λ A → Δ ,⋆ K ⊢ A)
             (trans (sym (evalCRSubst idCR (substNf-lemma σ⋆ (embNf B))))
                    (substNf-lemma' (⋆.subst (⋆.exts (embNf ∘ σ⋆)) (embNf B))))
             (subst (extsNf σ⋆) (exts⋆ σ⋆ σ) N))
subst {Φ}{Ψ}{Γ}{Δ} σ⋆ σ {J} (_·⋆_ {K = K}{B = B} L M) =
  substEq (λ A → Δ ⊢ A)
          (trans refl
                 (sym (subst[]Nf' σ⋆ M B)) )
          (subst σ⋆ σ L ·⋆ substNf σ⋆ M)
subst {Φ}{Ψ}{Γ}{Δ} σ⋆ σ (wrap1 {K = K} pat arg term) = wrap1
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
               (μ1 ·_)
               (completeness (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat))))))
         (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf arg))))))
    (subst σ⋆ σ term))
subst {Φ}{Ψ}{Γ}{Δ} σ⋆ σ (unwrap1 {pat = pat}{arg} term)       = substEq
  (Δ ⊢_)
  (sym  -- the same but backwards
    (trans
       (sym (substNf-nf σ⋆ (embNf pat · (μ1 · embNf pat) · embNf arg)))
       (AppCR
         (AppCR
           (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat))))
           (cong
               (μ1 ·_)
               (completeness (soundness (⋆.subst (embNf ∘ σ⋆) (embNf pat))))))
         (fund idCR (soundness (⋆.subst (embNf ∘ σ⋆) (embNf arg)))))))
  (unwrap1 (subst σ⋆ σ term))
subst σ⋆ σ (con c) = con (substTermCon σ⋆ c)
subst {Φ}{Ψ}{Γ}{Δ} σ⋆ σ (builtin bn σ' X) = let _ ,, _ ,, A = SIG bn in substEq
  (Δ ⊢_)
  (substNf-comp σ' σ⋆ A)
  (builtin bn (substNf σ⋆ ∘ σ') (substTel σ⋆ σ X))
subst σ⋆ x (error A) = error (substNf σ⋆ A)
\end{code}

\begin{code}
substcons : ∀{Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → (t : Δ ⊢ substNf σ⋆ A)
    ---------------------
  → (∀ {B : Φ ⊢Nf⋆ *} → Γ , A ∋ B → Δ ⊢ substNf σ⋆ B)
substcons σ⋆ σ t Z     = t
substcons σ⋆ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀ {Φ Γ} {A B : Φ ⊢Nf⋆ *}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {Φ}{Γ}{A}{B} b a =
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
_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
_[_]⋆ {Φ}{Γ}{K}{B} b A =
          subst (substNf-cons (ne ∘ `) A)
                 ( (λ {(T {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (trans (trans (sym (stability A')) (sym (reifyCR (ren-eval (embNf A') (λ x → idext idCR (embNf (substNf-cons (ne ∘ `) A x))) S)))) (sym (reifyCR (evalCRSubst (λ x → idext idCR (embNf (substNf-cons (ne ∘ `) A x))) (ren-embNf S A'))))) (reifyCR (symCR {K = *} (subst-eval (embNf (renNf S A')) idCR (embNf ∘ (substNf-cons (ne ∘ `) A))))))
                                     (` x)}))
                 b
\end{code}
