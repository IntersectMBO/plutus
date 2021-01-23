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
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Type.BetaNormal.Equality
\end{code}

## Renaming

\begin{code}
Ren : ∀{Φ Ψ} → ⋆.Ren Φ Ψ → Ctx Φ → Ctx Ψ → Set
Ren ρ⋆ Γ Δ = (∀ {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ∋ renNf ρ⋆ A)

ext : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    -------------------------------
  → Ren ρ⋆ (Γ , B) (Δ , renNf ρ⋆ B)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)
\end{code}

\begin{code}
ext⋆ : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → ∀ {K}
    --------------------------------
  → Ren (⋆.ext ρ⋆) (Γ ,⋆ K) (Δ ,⋆ K)
ext⋆ ρ⋆ ρ (T {A = A} x) = conv∋
  refl
  (weakenNf-renNf ρ⋆ A)
  (T (ρ x))
\end{code}

\begin{code}
renTermCon : ∀ {Φ Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
    -----------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (renNf ρ⋆ A ))
renTermCon ρ⋆ (integer i)    = integer i
renTermCon ρ⋆ (bytestring b) = bytestring b
renTermCon ρ⋆ (string s)     = string s
renTermCon ρ⋆ (bool b)       = bool b
renTermCon ρ⋆ (char c)       = char c
renTermCon ρ⋆ unit           = unit
\end{code}

\begin{code}
ren : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
    -----------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ renNf ρ⋆ A )
ren ρ⋆ ρ (` x)    = ` (ρ x)
ren ρ⋆ ρ (ƛ N)    = ƛ (ren ρ⋆ (ext ρ⋆ ρ) N)
ren ρ⋆ ρ (L · M)  = ren ρ⋆ ρ L · ren ρ⋆ ρ M 
ren ρ⋆ ρ (Λ N)    = Λ (ren (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N)
ren ρ⋆ ρ (_·⋆_ {B = B} t A) = conv⊢
  refl
  (sym (ren[]Nf ρ⋆ B A))
  (ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A)
ren ρ⋆ ρ (wrap A B M) = wrap
  (renNf ρ⋆ A)
  (renNf ρ⋆ B)
  (conv⊢ refl (ren-nf-μ ρ⋆ A B) (ren ρ⋆ ρ M))
ren ρ⋆ ρ (unwrap {A = A}{B} M) = conv⊢
  refl
  (sym (ren-nf-μ ρ⋆ A B))
  (unwrap (ren ρ⋆ ρ M)) 
ren ρ⋆ ρ (con c) = con (renTermCon ρ⋆ c)
ren ρ⋆ ρ (ibuiltin b) = conv⊢ refl (itype-ren b ρ⋆) (ibuiltin b)
ren ρ⋆ ρ (error A) = error (renNf ρ⋆ A)
\end{code}

\begin{code}
weaken : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weaken t = conv⊢
  refl
  (renNf-id _)
  (ren id (conv∋ refl (sym (renNf-id _)) ∘ S) t)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K}
  → Γ ⊢ A
    ------------------
  → Γ ,⋆ K ⊢ weakenNf A
weaken⋆ t = ren S (λ α → _∋_.T α) t
\end{code}

## Substitution

\begin{code}
Sub : ∀{Φ Ψ} → SubNf Φ Ψ → Ctx Φ → Ctx Ψ → Set
Sub σ⋆ Γ Δ = (∀ {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ⊢ subNf σ⋆ A)

exts : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    ---------------------------------
  → Sub σ⋆ (Γ , B) (Δ , subNf σ⋆ B)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S α) = weaken (σ α)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → ∀ {K}
    --------------------------------
  → Sub (extsNf σ⋆) (Γ ,⋆ K) (Δ ,⋆ K)
exts⋆ σ⋆ σ {K}(T {A = A} α) = conv⊢
  refl
  (weakenNf-subNf σ⋆ A)
  (weaken⋆ (σ α))
\end{code}

\begin{code}
subTermCon : ∀ {Φ Ψ}
  → (σ⋆ : SubNf Φ Ψ)
    ------------------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → TermCon A → TermCon (subNf σ⋆ A ))
subTermCon σ⋆ (integer i)    = integer i
subTermCon σ⋆ (bytestring b) = bytestring b
subTermCon σ⋆ (string s)     = string s
subTermCon σ⋆ (bool b)       = bool b
subTermCon σ⋆ (char c)       = char c
subTermCon σ⋆ unit           = unit
\end{code}

\begin{code}
sub : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
    -------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ subNf σ⋆ A)
sub σ⋆ σ (` k)                     = σ k
sub σ⋆ σ (ƛ N)                     = ƛ (sub σ⋆ (exts σ⋆ σ) N)
sub σ⋆ σ (L · M)                   = sub σ⋆ σ L · sub σ⋆ σ M
sub σ⋆ σ (Λ {B = B} N) =
  Λ (conv⊢ refl (sub-nf-Π σ⋆ B) (sub (extsNf σ⋆) (exts⋆ σ⋆ σ) N))
sub σ⋆ σ (_·⋆_ {B = B} L M) = conv⊢
  refl
  (sym (sub[]Nf' σ⋆ M B))
  (sub σ⋆ σ L ·⋆ subNf σ⋆ M)
sub σ⋆ σ (wrap A B M) = wrap
  (subNf σ⋆ A)
  (subNf σ⋆ B)
  (conv⊢ refl (sub-nf-μ σ⋆ A B) (sub σ⋆ σ M))
sub σ⋆ σ (unwrap {A = A}{B} M) = conv⊢
  refl
  (sym (sub-nf-μ σ⋆ A B))
  (unwrap (sub σ⋆ σ M))
sub σ⋆ σ (con c) = con (subTermCon σ⋆ c)
sub σ⋆ σ (ibuiltin b) = conv⊢ refl (itype-sub b σ⋆) (ibuiltin b)
sub σ⋆ σ (error A) = error (subNf σ⋆ A)
\end{code}

\begin{code}
subcons : ∀{Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → (t : Δ ⊢ subNf σ⋆ A)
    ---------------------
  → (∀ {B : Φ ⊢Nf⋆ *} → Γ , A ∋ B → Δ ⊢ subNf σ⋆ B)
subcons σ⋆ σ t Z     = t
subcons σ⋆ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → Γ , B ⊢ A
  → Γ ⊢ B 
    -----
  → Γ ⊢ A
_[_] {A = A}{B} b a = conv⊢ refl
  (subNf-id A)
  (sub ( ne ∘ `)
         (subcons (ne ∘ `)
                    (conv⊢ refl (sym (subNf-id _)) ∘ `)
                    (conv⊢ refl (sym (subNf-id B)) a))
         b)
\end{code}

\begin{code}
lem : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}{A : Φ ⊢Nf⋆ K} → (x : Γ ,⋆ K ∋ B) → 
  Γ ⊢ subNf (subNf-cons (λ x₁ → ne (` x₁)) A) B
lem (T x) = conv⊢
  refl
  (weakenNf[] _ _)
  (` x)

_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
_[_]⋆ b A = sub
  (subNf-cons (ne ∘ `) A)
  lem
  b
\end{code}
