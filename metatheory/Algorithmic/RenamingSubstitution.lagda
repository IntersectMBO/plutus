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
ext⋆ ρ⋆ ρ (T x) = conv∋ (weakenNf-renNf ρ⋆ _) (T (ρ x))
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
    -----------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ renNf ρ⋆ A )

renTel : ∀ {Φ Φ' Γ Γ' Δ}
 → (ρ⋆ : ⋆.Ren Φ Φ')
 → (ρ : Ren ρ⋆ Γ Γ')
 → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
 → {As : List (Δ ⊢Nf⋆ *)}
 → Tel Γ Δ σ As
 → Tel Γ' Δ (renNf ρ⋆ ∘ σ) As

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
weaken x = conv⊢ (renNf-id _) (ren id (conv∋ (sym (renNf-id _)) ∘ S) x)
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
    ---------------------------------
  → Sub σ⋆ (Γ , B) (Δ , substNf σ⋆ B)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S x) = weaken (σ x)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → ∀ {K}
    --------------------------------
  → Sub (extsNf σ⋆) (Γ ,⋆ K) (Δ ,⋆ K)
exts⋆ σ⋆ σ {K}(T {A = A} x) = conv⊢ (weakenNf-substNf σ⋆ A) (weaken⋆ (σ x))
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
    -------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ substNf σ⋆ A)

substTel σ⋆ σ      {As = []}     _         = _
substTel σ⋆ σ {σ'} {As = A ∷ As} (M ,, Ms) =
  conv⊢ (sym (substNf-comp σ' σ⋆ A)) (subst σ⋆ σ M) ,, substTel σ⋆ σ Ms

subst σ⋆ σ (` k)                     = σ k
subst σ⋆ σ (ƛ x N)                   = ƛ x (subst σ⋆ (exts σ⋆ σ) N)
subst σ⋆ σ (L · M)                   = subst σ⋆ σ L · subst σ⋆ σ M
subst σ⋆ σ (Λ x {B = B} N) =
  Λ x (conv⊢ (subst-nf-Π σ⋆ B) (subst (extsNf σ⋆) (exts⋆ σ⋆ σ) N))
subst σ⋆ σ (_·⋆_ {B = B} L M) =
  conv⊢ (sym (subst[]Nf' σ⋆ M B)) (subst σ⋆ σ L ·⋆ substNf σ⋆ M)
subst σ⋆ σ (wrap1 pat arg term) = wrap1
  (substNf σ⋆ pat)
  (substNf σ⋆ arg)
  (conv⊢ (subst-nf-μ σ⋆ pat arg) (subst σ⋆ σ term))
subst σ⋆ σ (unwrap1 {pat = pat}{arg} term) =
  conv⊢ (sym  (subst-nf-μ σ⋆ pat arg)) (unwrap1 (subst σ⋆ σ term))
subst σ⋆ σ (con c) = con (substTermCon σ⋆ c)
subst σ⋆ σ (builtin bn σ' X) = let _ ,, _ ,, A = SIG bn in
  conv⊢ (substNf-comp σ' σ⋆ A) (builtin bn (substNf σ⋆ ∘ σ') (substTel σ⋆ σ X))
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
_[_] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → Γ , B ⊢ A
  → Γ ⊢ B 
    -----
  → Γ ⊢ A
_[_] {A = A}{B} b a = conv⊢
  (substNf-id A)
  (subst ( ne ∘ `)
         (substcons (ne ∘ `)
                    (conv⊢ (sym (substNf-id _)) ∘ `)
                    (conv⊢ (sym (substNf-id B)) a))
         b)
\end{code}

\begin{code}
lem : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}{A : Φ ⊢Nf⋆ K} → (x : Γ ,⋆ K ∋ B) → 
  Γ ⊢ substNf (substNf-cons (λ x₁ → ne (` x₁)) A) B
lem (T x) = conv⊢ (weakenNf[] _ _) (` x)

_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
_[_]⋆ b A = subst
  (substNf-cons (ne ∘ `) A)
  lem
  b
\end{code}
