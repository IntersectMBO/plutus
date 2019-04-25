\begin{code}
module AlgorithmicRed.Term.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
open import Data.Unit

open import Type
open import Type.BetaNormal
open import Type.Reduction
import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE.RenamingSubstitution
open import Type.Equality
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import AlgorithmicRed.Term
\end{code}


## Renaming
\begin{code}
Ren : ∀ Γ Δ → ⋆.Ren ∥ Γ ∥ ∥ Δ ∥ → Set
Ren Γ Δ ρ = ∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ A
\end{code}


\begin{code}
ext : ∀ {Γ Δ}
  → (ρ⋆ : ⋆.Ren ∥ Γ ∥ ∥ Δ ∥)
  → Ren Γ Δ ρ⋆
    ------------------------------------------------------------
  → (∀ {K }{B : ∥ Γ ∥ ⊢Nf⋆ K} → Ren (Γ , B) (Δ , renameNf ρ⋆ B) ρ⋆)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
ext⋆ : ∀ {Γ Δ}
  → (ρ⋆ : ⋆.Ren ∥ Γ ∥ ∥ Δ ∥)
  → Ren Γ Δ ρ⋆
    ----------------------------------------
  → ∀ {K} → Ren (Γ ,⋆ K) (Δ ,⋆ K) (⋆.ext ρ⋆)
ext⋆ {Γ}{Δ} ρ⋆ ρ {K}{A} (T x) =
  substEq (λ A → Δ ,⋆ K ∋ A)
          (trans (sym (renameNf-comp _)) (renameNf-comp _))
          (T (ρ x))
\end{code}

\begin{code}
renameTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    -----------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (renameNf ρ⋆ A ))
renameTermCon ρ⋆ (integer i)    = integer i
renameTermCon ρ⋆ (bytestring b) = bytestring b
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.List

rename : ∀ {Γ Δ}
  → (ρ⋆ : ⋆.Ren ∥ Γ ∥ ∥ Δ ∥)
  → Ren Γ Δ ρ⋆
    ------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Δ ⊢ renameNf ρ⋆ A )

renameTel : ∀ {Γ Γ' Δ}
 → (ρ⋆ : ⋆.Ren ∥ Γ ∥ ∥ Γ' ∥)
 → Ren Γ Γ' ρ⋆
 → {σ : ∀ {J} → Δ ∋⋆ J → ∥ Γ ∥ ⊢Nf⋆ J}
 → {As : List (Δ ⊢Nf⋆ *)}
 → Tel Γ Δ σ As
 → Tel Γ' Δ (renameNf ρ⋆ ∘ σ) As

renameTel ρ⋆ ρ {As = []}     _         = _
renameTel ρ⋆ ρ {σ = σ}{As = A ∷ As} (R ,, (p ,, q ,, r ,, s) ,, M ,, Ms) =
  renameNf ρ⋆ R
  ,,
  (⋆.rename ρ⋆ p
   ,,
   substEq
     (_—→⋆ ⋆.rename ρ⋆ p)
     (trans
       (sym (⋆.rename-subst (embNf A)))
       (⋆.subst-cong (λ x → sym (rename-embNf ρ⋆ (σ x))) (embNf A)))
     (rename—→⋆ ρ⋆ q)
   ,,
   renameValue⋆ ρ⋆ r
   ,,
   trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
  ,,
  rename ρ⋆ ρ M 
  ,,
  renameTel ρ⋆ ρ Ms
  
rename ρ⋆ ρ (` x)    = ` (ρ x)
rename ρ⋆ ρ (ƛ {A' = A'} (A ,, p ,, q ,, r) N)    = ƛ (
  ⋆.rename ρ⋆ A
  ,,
  rename—→⋆ ρ⋆ p
  ,,
  renameValue⋆ ρ⋆ q
  ,,
  trans (rename-embNf ρ⋆ A') (cong (⋆.rename ρ⋆) r)) (rename ρ⋆ (ext ρ⋆ ρ) N)
rename ρ⋆ ρ (L · M)  = rename ρ⋆ ρ L · rename ρ⋆ ρ M 
rename ρ⋆ ρ (Λ N)    = Λ (rename (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N )
rename {Γ}{Δ} ρ⋆ ρ (_·⋆_ {B = B} t A {R} (p ,, q ,, r ,, s)) = _·⋆_
  (rename ρ⋆ ρ t)
  (renameNf ρ⋆ A)
  (⋆.rename ρ⋆ p
  ,,
  substEq
    (_—→⋆ ⋆.rename ρ⋆ p)
    (trans
      (sym (⋆.rename-subst (embNf B)))
      (trans
        (trans
          (⋆.subst-cong (sym ∘ ⋆.rename-subst-cons ρ⋆ (embNf A)) (embNf B))
          (⋆.subst-rename (embNf B)))
        (cong₂
            ⋆._[_]
            (sym (rename-embNf (⋆.ext ρ⋆) B))
            (sym (rename-embNf ρ⋆ A)))))
    (rename—→⋆ ρ⋆ q)
  ,, renameValue⋆ ρ⋆ r
  ,, trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
rename ρ⋆ ρ (wrap1 pat arg {R} (p ,, q ,, r ,, s) t) = wrap1
  _
  _
  (⋆.rename ρ⋆ p
   ,,
   substEq
     (_—→⋆ ⋆.rename ρ⋆ p)
     (cong₂
       (λ t u → t · (μ1 · t) · u)
       (sym (rename-embNf ρ⋆ pat))
       (sym (rename-embNf ρ⋆ arg)))
     (rename—→⋆ ρ⋆ q)
   ,,
   renameValue⋆ ρ⋆ r
   ,,
   trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
  (rename ρ⋆ ρ t)
rename ρ⋆ ρ (unwrap1 {pat = pat}{arg = arg} t {R = R} (p ,, q ,, r ,, s)) = unwrap1
  (rename ρ⋆ ρ t)
  (⋆.rename ρ⋆ p
   ,,
   substEq
     (_—→⋆ ⋆.rename ρ⋆ p)
     (cong₂
       (λ t u → t · (μ1 · t) · u)
       (sym (rename-embNf ρ⋆ pat))
       (sym (rename-embNf ρ⋆ arg)))
     (rename—→⋆ ρ⋆ q)
   ,,
   renameValue⋆ ρ⋆ r
   ,,
   trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
rename ρ⋆ ρ (con cn) = con (renameTermCon ρ⋆ cn)
rename {Γ} {Δ} ρ⋆ ρ (builtin bn σ X {R = R} (p ,, q ,, r ,, s)) = builtin
  bn
  (renameNf ρ⋆ ∘ σ)
  (renameTel ρ⋆ ρ X)
  (⋆.rename ρ⋆ p
   ,,
   substEq
     (_—→⋆ ⋆.rename ρ⋆ p)
     (trans
       (sym (⋆.rename-subst (embNf (proj₂ (proj₂ (SIG bn))))))
       (⋆.subst-cong
         (λ x → sym (rename-embNf ρ⋆ (σ x)))
         (embNf (proj₂ (proj₂ (SIG bn))))))
     (rename—→⋆ ρ⋆ q)
   ,,
   renameValue⋆ ρ⋆ r
   ,,
   trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
rename ρ⋆ ρ (error A {R = R} (p ,, q ,, r ,, s)) = error
  (⋆.rename ρ⋆ A)
  (⋆.rename ρ⋆ p
   ,,
   rename—→⋆ ρ⋆ q
   ,,
   renameValue⋆ ρ⋆ r
   ,,
   trans (rename-embNf ρ⋆ R) (cong (⋆.rename ρ⋆) s))
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
Sub : ∀ Γ Δ → (∀{J} → ∥ Γ ∥ ∋⋆ J → ∥ Δ ∥ ⊢Nf⋆ J) → Set
Sub Γ Δ σ = ∀ {J} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ⊢ substNf σ A
\end{code}


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
{-
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
          {! trans (sym (⋆.rename-subst A))
                 (⋆.subst-rename A) !}
          (weaken⋆ (σ x))
-}
\end{code}

\begin{code}
{-
substTermCon : ∀ {Φ Ψ}
  → (σ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    ------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.subst σ⋆ A ))
substTermCon σ⋆ (integer s i p)    = integer s i p
substTermCon σ⋆ (bytestring s b p) = bytestring s b p
substTermCon σ⋆ (size s)           = size s
-}
\end{code}


\begin{code}
{-
subst : ∀ {Γ Δ}
  → (σ⋆ : ∀ {K} → ∥ Γ ∥ ∋⋆ K → ∥ Δ ∥ ⊢⋆ K)
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → (∀ {J} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Δ ⊢ ⋆.subst σ⋆ A)

substTel : ∀ {Γ Γ' Δ}
 → (σ⋆ : ⋆.Sub ∥ Γ ∥ ∥ Γ' ∥)
 → Sub Γ Γ' σ⋆
 → {σ' : ⋆.Sub Δ ∥ Γ ∥}
 → {As : List (Δ ⊢⋆ *)}
 → Tel Γ Δ σ' As
 → Tel Γ' Δ (⋆.subst σ⋆ ∘ σ') As
substTel σ⋆ σ {As = []}     _         = _
substTel σ⋆ σ {As = A ∷ As} (M ,, Ms) =
  substEq (_ ⊢_) (sym (⋆.subst-comp A)) (subst σ⋆ σ M) ,, substTel σ⋆ σ Ms

subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ N)                     = ƛ (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst σ⋆ σ (Λ N)                     = Λ (subst (⋆.exts σ⋆) (exts⋆ σ⋆ σ) N)
subst {Γ}{Δ} σ⋆ σ (_·⋆_ {B = B} L M) =
  substEq (λ A → Δ ⊢ A)
          (trans (sym (⋆.subst-comp B))
                 (trans (⋆.subst-cong (⋆.subst-subst-cons σ⋆ M)
                                    B)
                        (⋆.subst-comp B)))
          (subst σ⋆ σ L ·⋆ ⋆.subst σ⋆ M)
subst σ⋆ σ (wrap1 pat arg t) = wrap1 _ _ (subst σ⋆ σ t)
subst σ⋆ σ (unwrap1 t)       = unwrap1 (subst σ⋆ σ t)
subst σ⋆ σ (con cn) = con (substTermCon σ⋆ cn)
subst {Γ}{Γ'} σ⋆ σ (builtin bn σ' tel ) = substEq
  (Γ' ⊢_)
  (⋆.subst-comp (proj₂ (proj₂ (SIG bn))))
  (builtin bn (⋆.subst σ⋆ ∘ σ') (substTel σ⋆ σ tel))
subst σ⋆ σ (error A) = error (⋆.subst σ⋆ A)
-}
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
{-
_[_] : ∀ {J Γ} {A B : ∥ Γ ∥ ⊢⋆ J}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_]  {J} {Γ}{A}{B} t s =
  substEq (λ A → Γ ⊢ A)
          (⋆.subst-id A)
          (subst `
                 (substcons `
                            (λ x → substEq (λ A → Γ ⊢ A)
                                           (sym (⋆.subst-id _))
                                           (` x))
                            (substEq (λ A → Γ ⊢ A) (sym (⋆.subst-id B)) s))
                 t) 
-}
\end{code}

\begin{code}
{-
_[_]⋆ : ∀ {J Γ K} {B : ∥ Γ ,⋆ K ∥ ⊢⋆ J}
        → Γ ,⋆ K ⊢ B
        → (A : ∥ Γ ∥ ⊢⋆ K)
          ---------
        → Γ ⊢ B ⋆.[ A ]
_[_]⋆ {J}{Γ}{K}{B} t A =
  subst (⋆.subst-cons ` A)
        (λ{(T {A = A'} x) → substEq (λ A → Γ ⊢ A)
                                     (trans (sym (⋆.subst-id A'))
                                     (⋆.subst-rename A'))
                                     (` x)})
          t
-}
\end{code}
