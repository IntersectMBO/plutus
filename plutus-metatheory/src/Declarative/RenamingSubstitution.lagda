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
ren _ ρ (` x)    = ` (ρ x)
ren _ ρ (ƛ N)    = ƛ (ren _ (ext _ ρ) N)
ren _ ρ (L · M)  = ren _ ρ L · ren _ ρ M 
ren _ ρ (Λ N)    = Λ (ren _ (ext⋆ _ ρ) N )
ren {Δ = Δ} ρ⋆ ρ (_·⋆_ {B = B} t A) = conv⊢
  refl
  (trans (sym (⋆.sub-ren B))
         (trans (⋆.sub-cong (⋆.ren-sub-cons ρ⋆ A) B)
                (⋆.ren-sub B)))
  (_·⋆_ (ren _ ρ t) (⋆.ren ρ⋆ A))
ren _ ρ (wrap A B t) = wrap
  _
  _
  (conv⊢
    refl
    (⋆.ren-μ _ A B)
    (ren _ ρ t))
ren _ ρ (unwrap t) = conv⊢
  refl
  (sym (⋆.ren-μ _ _ _))
  (unwrap (ren _ ρ t))
ren _ ρ (conv p t) = conv (ren≡β _ p) (ren _ ρ t)
ren ρ⋆ ρ (con cn) = con (renTermCon ρ⋆ cn)
ren ρ⋆ _ (ibuiltin b) = conv⊢ refl (itype-ren b ρ⋆) (ibuiltin b)
ren _ _ (error A) = error (⋆.ren _ A)
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
Sub {Φ} Γ Δ σ = {A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.sub σ A
\end{code}

\begin{code}
exts : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A :  Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.sub σ⋆ A)
    ---------------------------------------------------
  → ({A B : Φ ⊢⋆ *}
     → Γ , B ∋ A
     -------------------------------
     → Δ , ⋆.sub σ⋆ B ⊢ ⋆.sub σ⋆ A)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.sub σ⋆ A)
    ---------------------------------------------------
  → (∀ {K}{A : Φ ,⋆ K ⊢⋆ *}
     → Γ ,⋆ K ∋ A 
       -------------------------------
     → Δ ,⋆ K ⊢ ⋆.sub (⋆.exts σ⋆) A )
exts⋆ {Δ = Δ} _ σ {K}(T {A = A} x) = conv⊢
  refl
  (trans (sym (⋆.ren-sub A)) (⋆.sub-ren A))
  (weaken⋆ (σ x))
\end{code}

\begin{code}
subTermCon : ∀ {Φ Ψ}
  → (σ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    ------------------------
  → ({A : Φ ⊢⋆ *} → TermCon A → TermCon (⋆.sub σ⋆ A ))
subTermCon _ (integer i)    = integer i
subTermCon _ (bytestring b) = bytestring b
subTermCon _ (string s)     = string s
subTermCon _ (bool b)       = bool b
subTermCon _ (char c)       = char c
subTermCon _ unit           = unit

\end{code}


\begin{code}
sub : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀ {K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.sub σ⋆ A)
    ---------------------------------------------------
  → ({A : Φ ⊢⋆ *} → Γ ⊢ A → Δ ⊢ ⋆.sub σ⋆ A)
sub _ σ (` k)                       = σ k
sub _ σ (ƛ N)                       = ƛ (sub _ (exts _ σ) N)
sub _ σ (L · M)                     = sub _ σ L · sub _ σ M
sub _ σ (Λ N)                       = Λ (sub _ (exts⋆ _ σ) N)
sub {Δ = Δ} σ⋆ σ (_·⋆_ {B = B} L A) = conv⊢
  refl
  (trans (sym (⋆.sub-comp B))
         (trans (⋆.sub-cong (⋆.sub-sub-cons σ⋆ A) B)
                (⋆.sub-comp B)))
  (_·⋆_ (sub σ⋆ σ L) (⋆.sub σ⋆ A))
sub _ σ (wrap A B t)                =
  wrap _ _ (conv⊢ refl (⋆.sub-μ _ A B) (sub _ σ t))
sub σ⋆ σ (unwrap {A = A}{B} t)                  =
 conv⊢ refl (sym (⋆.sub-μ σ⋆ A B)) (unwrap (sub σ⋆ σ t))
sub _ σ (conv p t)                  = conv (sub≡β _ p) (sub _ σ t)
sub σ⋆ σ (con cn)                   = con (subTermCon σ⋆ cn)
sub σ⋆ _ (ibuiltin b) = conv⊢ refl (itype-sub b σ⋆) (ibuiltin b)
sub _ σ (error A) = error (⋆.sub _ A)
\end{code}

\begin{code}
subcons : ∀{Φ Ψ Γ Δ} →
  (σ⋆ : ∀{K} → Φ  ∋⋆ K → Ψ ⊢⋆ K)
  → ({A : Φ ⊢⋆ *} → Γ ∋ A → Δ ⊢ ⋆.sub σ⋆ A)
  → {A : Φ ⊢⋆ *}
  → (t : Δ ⊢ ⋆.sub σ⋆ A)
    ---------------------
  → ({B : Φ ⊢⋆ *} → Γ , A ∋ B → Δ ⊢ ⋆.sub σ⋆ B)
subcons _ σ t Z     = t
subcons _ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀ {Φ Γ} {A B : Φ ⊢⋆ *}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_]  {Γ = Γ}{A}{B} t s = conv⊢
  refl
  (⋆.sub-id A)
  (sub
    _
    (subcons ` (λ x → ` (conv∋ refl (sym (⋆.sub-id _)) x))
    (conv⊢ refl (sym (⋆.sub-id B)) s)) t)
\end{code}

\begin{code}
_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢⋆ K)
          ---------
        → Γ ⊢ B ⋆.[ A ]
_[_]⋆ {J}{Γ = Γ}{K}{B} t A = sub
  _
  (λ {(T {A = A'} x) → conv⊢
    refl
    (trans (sym (⋆.sub-id A')) (⋆.sub-ren A'))
    (` x)})
  t
\end{code}
