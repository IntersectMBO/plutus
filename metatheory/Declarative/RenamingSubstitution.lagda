\begin{code}
module Declarative.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
open import Data.Unit

open import Type
import Type.RenamingSubstitution as ⋆
open import Type.Equality
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
open import Declarative
\end{code}


## Renaming
\begin{code}
Ren : ∀ {Φ Ψ}(Γ : Ctx Φ)(Δ : Ctx Ψ) → ⋆.Ren Φ Ψ → Set
Ren {Φ} Γ Δ ρ = {A : Φ ⊢⋆ *} → Γ ∋ A → Δ ∋ ⋆.ren ρ A
\end{code}

\begin{code}
ext : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → Ren Γ Δ ρ⋆
  → {B : Φ ⊢⋆ *}
    ----------------------------------
  → Ren (Γ , B) (Δ , ⋆.ren ρ⋆ B) ρ⋆
ext _ ρ Z     = Z 
ext _ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
ext⋆ : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → Ren Γ Δ ρ⋆
  →  ∀ {K}
    --------------------------------
  → Ren (Γ ,⋆ K) (Δ ,⋆ K) (⋆.ext ρ⋆)
ext⋆ ρ⋆ ρ (T x) = conv∋
  refl
  (trans (sym (⋆.ren-comp _)) (⋆.ren-comp _))
  (T (ρ x))
\end{code}

\begin{code}
renTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    -----------------------------------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.ren ρ⋆ A ))
renTermCon ρ⋆ (integer i)    = integer i
renTermCon ρ⋆ (bytestring b) = bytestring b
renTermCon ρ⋆ (string s)     = string s
renTermCon ρ⋆ (bool b)       = bool b
renTermCon ρ⋆ (char c)       = char c
renTermCon ρ⋆ unit           = unit

\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.List
ren : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → Ren Γ Δ ρ⋆
    ------------------------
  → ({A : Φ ⊢⋆ *} → Γ ⊢ A → Δ ⊢ ⋆.ren ρ⋆ A)

renTel : ∀ {Φ Φ' Γ Γ' Δ}
 → (ρ⋆ : ⋆.Ren Φ Φ')
 → Ren Γ Γ' ρ⋆
 → {σ : ⋆.Sub Δ Φ}
 → {As : List (Δ ⊢⋆ *)}
 → Tel Γ Δ σ As
 → Tel Γ' Δ (⋆.ren ρ⋆ ∘ σ) As

renTel _ ρ {As = []}     []       = []
renTel _ ρ {As = A ∷ As} (M ∷ Ms) =
  conv⊢ refl (sym (⋆.ren-subst A)) (ren _ ρ M) ∷ renTel _ ρ Ms

ren _ ρ (` x)    = ` (ρ x)
ren _ ρ (ƛ N)    = ƛ (ren _ (ext _ ρ) N)
ren _ ρ (L · M)  = ren _ ρ L · ren _ ρ M 
ren _ ρ (Λ N)    = Λ (ren _ (ext⋆ _ ρ) N )
ren {Δ = Δ} ρ⋆ ρ (_·⋆_ {B = B} t A) = conv⊢
  refl
  (trans (sym (⋆.subst-ren B))
         (trans (⋆.subst-cong (⋆.ren-subst-cons ρ⋆ A) B)
                (⋆.ren-subst B)))
  (_·⋆_ (ren _ ρ t) (⋆.ren ρ⋆ A))
ren _ ρ (wrap1 pat arg t) = wrap1 _ _ (ren _ ρ t)
ren _ ρ (unwrap1 t)       = unwrap1 (ren _ ρ t)
ren _ ρ (conv p t) = conv (ren≡β _ p) (ren _ ρ t)
ren ρ⋆ ρ (con cn)   = con (renTermCon ρ⋆ cn)
ren {Δ = Δ} ρ⋆ ρ (builtin bn σ X) = conv⊢
  refl
  (⋆.ren-subst (proj₂ (proj₂ (SIG bn))))
  (builtin bn (⋆.ren _ ∘ σ) (renTel _ ρ X))
ren _ ρ (error A) = error (⋆.ren _ A)
\end{code}

\begin{code}
weaken : ∀ {Φ Γ}{A B : Φ ⊢⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weaken {Γ = Γ}{A}{B} x = conv⊢
  refl
  (⋆.ren-id A)
  (ren _ (λ y → conv∋ refl (sym (⋆.ren-id _)) (S y)) x)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ Γ}{A : Φ ⊢⋆ *}{K}
  → Γ ⊢ A
    -------------------
  → Γ ,⋆ K ⊢ ⋆.weaken A
weaken⋆ x = ren _ T x
\end{code}

## Substitution
\begin{code}
Sub : ∀ {Φ}{Ψ} Γ Δ → ⋆.Sub Φ Ψ → Set
Sub {Φ} Γ Δ σ = {A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.subst σ A
\end{code}

\begin{code}
exts : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A :  Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → ({A B : Φ ⊢⋆ *}
     → Γ , B ∋ A
     -------------------------------
     → Δ , ⋆.subst σ⋆ B ⊢ ⋆.subst σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → (∀ {K}{A : Φ ,⋆ K ⊢⋆ *}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ ⋆.subst (⋆.exts σ⋆) A )
exts⋆ {Δ = Δ} _ σ {K}(T {A = A} x) = conv⊢
  refl
  (trans (sym (⋆.ren-subst A)) (⋆.subst-ren A))
  (weaken⋆ (σ x))
\end{code}

\begin{code}
substTermCon : ∀ {Φ Ψ}
  → (σ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    ------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.subst σ⋆ A ))
substTermCon _ (integer i)    = integer i
substTermCon _ (bytestring b) = bytestring b
substTermCon _ (string s)     = string s
substTermCon _ (bool b)       = bool b
substTermCon _ (char c)       = char c
substTermCon _ unit           = unit

\end{code}


\begin{code}
subst : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------------------------------------
  → ({A : Φ ⊢⋆ *} → Γ ⊢ A → Δ ⊢ ⋆.subst σ⋆ A)

substTel : ∀ {Φ Ψ Γ Γ' Δ}
 → (σ⋆ : ⋆.Sub Φ Ψ)
 → Sub Γ Γ' σ⋆
 → {σ' : ⋆.Sub Δ Φ}
 → {As : List (Δ ⊢⋆ *)}
 → Tel Γ Δ σ' As
 → Tel Γ' Δ (⋆.subst σ⋆ ∘ σ') As
substTel _ σ {As = []}     []       = []
substTel _ σ {As = A ∷ As} (M ∷ Ms) = 
  conv⊢ refl (sym (⋆.subst-comp A)) (subst _ σ M) ∷ substTel _ σ Ms
subst _ σ (` k)                       = σ k
subst _ σ (ƛ N)                       = ƛ (subst _ (exts _ σ) N)
subst _ σ (L · M)                     = subst _ σ L · subst _ σ M
subst _ σ (Λ N)                       = Λ (subst _ (exts⋆ _ σ) N)
subst {Δ = Δ} σ⋆ σ (_·⋆_ {B = B} L A) = conv⊢
  refl
  (trans (sym (⋆.subst-comp B))
         (trans (⋆.subst-cong (⋆.subst-subst-cons σ⋆ A) B)
                (⋆.subst-comp B)))
  (_·⋆_ (subst σ⋆ σ L) (⋆.subst σ⋆ A))
subst _ σ (wrap1 pat arg t)           = wrap1 _ _ (subst _ σ t)
subst _ σ (unwrap1 t)                 = unwrap1 (subst _ σ t)
subst _ σ (conv p t)                  = conv (subst≡β _ p) (subst _ σ t)
subst σ⋆ σ (con cn)                   = con (substTermCon σ⋆ cn)
subst {Φ}{Γ = Γ}{Γ'} σ⋆ σ (builtin bn σ' tel) = conv⊢
  refl
  (⋆.subst-comp (proj₂ (proj₂ (SIG bn))))
  (builtin bn (⋆.subst σ⋆ ∘ σ') (substTel σ⋆ σ tel))
subst _ σ (error A) = error (⋆.subst _ A)
\end{code}

\begin{code}
substcons : ∀{Φ Ψ Γ Δ} →
  (σ⋆ : ∀{K} → Φ  ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.subst σ⋆ A)
  → {A : Φ ⊢⋆ *}
  → (t : Δ ⊢ ⋆.subst σ⋆ A)
    ---------------------
  → ({B : Φ ⊢⋆ *} → Γ , A ∋ B → Δ ⊢ ⋆.subst σ⋆ B)
substcons _ σ t Z     = t
substcons _ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀ {Φ Γ} {A B : Φ ⊢⋆ *}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_]  {Γ = Γ}{A}{B} t s = conv⊢
  refl
  (⋆.subst-id A)
  (subst
    _
    (substcons ` (λ x → ` (conv∋ refl (sym (⋆.subst-id _)) x))
    (conv⊢ refl (sym (⋆.subst-id B)) s)) t)
\end{code}

\begin{code}
_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢⋆ K)
          ---------
        → Γ ⊢ B ⋆.[ A ]
_[_]⋆ {J}{Γ = Γ}{K}{B} t A = subst
  _
  (λ {(T {A = A'} x) → conv⊢
    refl
    (trans (sym (⋆.subst-id A')) (⋆.subst-ren A'))
    (` x)})
  t
\end{code}
