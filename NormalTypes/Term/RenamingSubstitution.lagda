\begin{code}
module NormalTypes.Term.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq; [_] to [_]≅)

open import Type
import Type.RenamingSubstitution as ⋆
open import Type.Reduction
open import Type.BetaNormal
open import Type.BetaNBE
open import NormalTypes.Term
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
          (trans (sym (renameNf-comp ρ⋆ S _)) (renameNf-comp S (⋆.ext ρ⋆) _))
          (T (ρ x))
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
rename {Γ}{Δ} ρ⋆ ρ (wrap {B = B} M) =
  wrap (substEq (Δ ⊢_)
                (rename[]Nf ρ⋆ B (μ B))
                (rename ρ⋆ ρ M))
rename {Γ}{Δ} ρ⋆ ρ (unwrap {B = B} M) =
  substEq (Δ ⊢_)
          (sym (rename[]Nf ρ⋆ B (μ B)))
          (unwrap (rename ρ⋆ ρ M))

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
          (trans (rename-readback (idext idPER (⋆.subst (embNf ∘ σ⋆) (embNf A))) S) (reify _ (transPER _ (renval-eval (⋆.subst (embNf ∘ σ⋆) (embNf A)) idPER S)
                                                                                                (transPER _ (transPER _ (subst-eval  (embNf A) (renPER S ∘ idPER) (embNf ∘ σ⋆)) (transPER _ (idext (λ {x → transPER _ (transPER _ (idext (λ x → renval-neV S (` x)) (embNf (σ⋆ x))) (symPER _ (rename-eval (embNf (σ⋆ x)) idPER S))) (symPER _ (evalPERSubst idPER (rename-embNf S (σ⋆ x))))}) (embNf A)) (symPER _ (subst-eval (embNf A) idPER (embNf ∘ renameNf S ∘ σ⋆))))) (evalPERSubst idPER (trans (⋆.subst-rename S (embNf ∘ extsNf σ⋆) (embNf A)) (cong (λ x → ⋆.subst (embNf ∘ extsNf σ⋆) x) (sym (rename-embNf S A)))))))))
          (weaken⋆ (σ x))
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
subst {Γ}{Δ} σ⋆ σ {J} (Λ {K = K}{B = B} N)                     = {!!}
{-  Λ (substEq (λ A → Δ ,⋆ _ ⊢ A)
             -- this is the property needed in subst[]Nf...
             (cong₂
                (λ (σ₁ : ∀ {K'} → (∥ Γ ∥ ,⋆ K) ∋⋆ K' → ∥ Δ ∥ ,⋆ K ⊢⋆ K')
                   (γ : ∀ {K'} → ∥ Δ ∥ ,⋆ K ∋⋆ K' → Val (∥ Δ ∥ ,⋆ K) K') →
                   eval (⋆.subst σ₁ (embNf B)) γ)
                {!σ⋆!} {!!}) -- (funiext (λ a → funext (λ { Z → {!stability!} ; (S x) → ≡-to-≅ (rename-embNf S (σ⋆ x))}))) (funiext (λ a → funext (λ { Z → refl ; (S x) → sym (rename-reflect a S (` x))}))))
             (subst (extsNf σ⋆) (exts⋆ σ⋆ σ) N)) -}
subst {Γ}{Δ} σ⋆ σ {J} (_·⋆_ {K = K}{B = B} L M) = {!subst σ⋆ σ L ·⋆ substNf σ⋆ M!}
{-  substEq (λ A → Δ ⊢ A)
          (sym (subst[]Nf σ⋆ M B))
          (subst σ⋆ σ L ·⋆ substNf σ⋆ M)  -}
subst {Γ}{Δ} σ⋆ σ (wrap {B = B} N) = {!!}
{-  wrap 
       (substEq (λ A → Δ ⊢ A)
                (subst[]Nf σ⋆ (μ B) B)
                (subst σ⋆ σ N)) -}
subst {Γ}{Δ} σ⋆ σ (unwrap {B = B} M) = {!!}
{-  substEq (λ A → Δ ⊢ A)
          (sym (subst[]Nf σ⋆ (μ B) B))
          (unwrap (subst σ⋆ σ M)) -}
\end{code}

\begin{code}
{-
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
          (subst  (nf ∘ `)
                  (substcons (nf ∘ `)
                             (λ x → substEq (λ A → Γ ⊢ A)
                                            (sym (substNf-id _))
                                            (` x))
                             (substEq (λ A → Γ ⊢ A) (sym (substNf-id B)) a))
                  b)
-}
\end{code}

\begin{code}
postulate
 _[_]⋆ : ∀ {J Γ K} {B : ∥ Γ ,⋆ K ∥ ⊢Nf⋆ J}
        → Γ ,⋆ K ⊢ B
        → (A : ∥ Γ ∥ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
{-
_[_]⋆ {J}{Γ}{K}{B} b A =
  substEq (λ A → Γ ⊢ A)
          (cong
             (λ (σ : ∀ {J} → _ ∋⋆ J → _ ⊢⋆ J) → 
                reify J (eval (⋆.subst σ (embNf B)) idEnv))
             (funiext (λ K → funext λ { Z → refl ; (S x) → {!!}}))) -- this goal is uninhabited: embNf (nf (` x)) ≠ ` x
          (subst (substNf-cons (nf ∘ `) A)
                 ( (λ {(T {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (sym (substNf-id A')) (substNf-renameNf S (substNf-cons (nf ∘ `) A) A'))
                                     (` x)}) )
                 b)
-}

\end{code}
