\begin{code}
module Algorithmic.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;cong₂)

open import Utils using (Kind;*)
open import Type using (Ctx⋆;_,⋆_;S)
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic using (Ctx;_∋_;conv∋;_⊢_;conv⊢)
open import Algorithmic.Signature using (btype-ren;btype-sub)
open Ctx
open _∋_
open _⊢_

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon

open import Type.BetaNormal.Equality using (renNf-id)
\end{code}

## Renaming

\begin{code}
Ren : ∀{Φ Ψ} → ⋆.Ren Φ Ψ → Ctx Φ → Ctx Ψ → Set
Ren ρ⋆ Γ Δ = {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ∋ renNf ρ⋆ A

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
renTermCon ρ⋆ unit           = unit
renTermCon ρ⋆ (pdata d)      = pdata d
renTermCon ρ⋆ (bls12-381-g1-element e) = bls12-381-g1-element e
renTermCon ρ⋆ (bls12-381-g2-element e) = bls12-381-g2-element e
renTermCon ρ⋆ (bls12-381-mlresult r)   = bls12-381-mlresult r
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
ren ρ⋆ ρ (_·⋆_/_ {B = B} t A refl) = conv⊢
  refl
  (sym (ren[]Nf ρ⋆ B A))
  (ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A / refl)
ren ρ⋆ ρ (wrap A B M) = wrap
  (renNf ρ⋆ A)
  (renNf ρ⋆ B)
  (conv⊢ refl (ren-nf-μ ρ⋆ A B) (ren ρ⋆ ρ M))
ren ρ⋆ ρ (unwrap {A = A}{B} M refl) = conv⊢
  refl
  (sym (ren-nf-μ ρ⋆ A B))
  (unwrap (ren ρ⋆ ρ M) refl) 
ren ρ⋆ ρ (con c) = con (renTermCon ρ⋆ c)
ren ρ⋆ ρ (builtin b / refl) = conv⊢ refl (btype-ren b ρ⋆) (builtin b / refl)
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
exts⋆ σ⋆ σ {K}(T {A = A} x) = conv⊢
  refl
  (weakenNf-subNf σ⋆ A)
  (weaken⋆ (σ x))
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
subTermCon σ⋆ unit           = unit
subTermCon σ⋆ (pdata d)      = pdata d
subTermCon σ⋆ (bls12-381-g1-element e) = bls12-381-g1-element e
subTermCon σ⋆ (bls12-381-g2-element e) = bls12-381-g2-element e
subTermCon σ⋆ (bls12-381-mlresult r)   = bls12-381-mlresult r
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
sub σ⋆ σ (_·⋆_/_ {B = B} L M refl) = conv⊢
  refl
  (sym (sub[]Nf' σ⋆ M B))
  (sub σ⋆ σ L ·⋆ subNf σ⋆ M / refl)
sub σ⋆ σ (wrap A B M) = wrap
  (subNf σ⋆ A)
  (subNf σ⋆ B)
  (conv⊢ refl (sub-nf-μ σ⋆ A B) (sub σ⋆ σ M))
sub σ⋆ σ (unwrap {A = A}{B} M refl) = conv⊢
  refl
  (sym (sub-nf-μ σ⋆ A B))
  (unwrap (sub σ⋆ σ M) refl)
sub σ⋆ σ (con c) = con (subTermCon σ⋆ c)
sub σ⋆ σ (builtin b / refl) = conv⊢ refl (btype-sub b σ⋆) (builtin b / refl)
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

# simply typed renaming

These are easier to reason about and show up in the CEK machine as
discharge is simply typed. Fully general rens/subs reasoning easily
gets bogged down with type coercions.

Note: This doesn't scale to substitution as we need to weaken by a
type var to go under a Λ.

\begin{code}
Renˢ : ∀{Φ} → Ctx Φ → Ctx Φ → Set
Renˢ Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

extˢ : ∀ {Φ Γ Δ}
  → (ρ : Renˢ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    -------------------------------
  → Renˢ (Γ , B) (Δ , B)
extˢ ρ Z     = Z
extˢ ρ (S x) = S (ρ x)

-- here we are manipulating the type contexts of the renaming but only
-- by extending them with the same kind
extˢ⋆ : ∀{Φ}{Γ Δ : Ctx Φ}
  → (ρ : Renˢ Γ Δ)
  → ∀ {K}
    ----------------------
  → Renˢ (Γ ,⋆ K) (Δ ,⋆ K)
extˢ⋆ ρ (T x) = T (ρ x)

renˢ : ∀ {Φ Γ Δ}
  → (ρ : Renˢ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    -----
  → Δ ⊢ A
renˢ ρ (` x)           = ` (ρ x)
renˢ ρ (ƛ M)           = ƛ (renˢ (extˢ ρ) M)
renˢ ρ (L · M)         = renˢ ρ L · renˢ ρ M
renˢ ρ (Λ M)           = Λ (renˢ (extˢ⋆ ρ) M)
renˢ ρ (M ·⋆ A / p) = renˢ ρ M ·⋆ A / p
renˢ ρ (wrap A B M)    = wrap A B (renˢ ρ M)
renˢ ρ (unwrap M p) = unwrap (renˢ ρ M) p
renˢ ρ (con c)         = con c
renˢ ρ (builtin b / p) = builtin b / p
renˢ ρ (error _) = error _

weakenˢ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weakenˢ M = renˢ S M

-- cannot define this using renˢ
{-
weaken⋆ˢ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K}
  → Γ ⊢ A
    ------------------
  → Γ ,⋆ K ⊢ weakenNf A
-}

extˢ-id : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}(x : Γ , A ∋ B)
  → extˢ id x ≡ x
extˢ-id Z     = refl
extˢ-id (S x) = refl

extˢ-comp : ∀ {Φ Γ Δ Θ}{A B : Φ ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(x : Γ , B ∋ A)
  → extˢ (ρ ∘ ρ') x ≡ extˢ ρ (extˢ ρ' x)
extˢ-comp Z     = refl
extˢ-comp (S x) = refl

extˢ⋆-id : ∀ {Φ Γ}{K}{A : Φ ,⋆ K ⊢Nf⋆ *}(x : Γ ,⋆ K ∋ A)
  → extˢ⋆ id x ≡ x
extˢ⋆-id (T x) = refl

extˢ⋆-comp : ∀ {Φ Γ Δ Θ}{K}{A : Φ ,⋆ K ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(x : Γ ,⋆ K ∋ A)
  → extˢ⋆ (ρ ∘ ρ') x ≡ extˢ⋆ ρ (extˢ⋆ ρ' x)
extˢ⋆-comp (T x) = refl

extˢ-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{A B}(x : Γ , A ∋ B)
            --------------------------------
          → extˢ ρ x ≡ extˢ ρ' x
extˢ-cong p Z = refl
extˢ-cong p (S x) = cong S (p x)

extˢ⋆-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{K B}(x : Γ ,⋆ K ∋ B)
            --------------------------------
          → extˢ⋆ ρ x ≡ extˢ⋆ ρ' x
extˢ⋆-cong p (T x) = cong T (p x)

renˢ-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{A}(M : Γ ⊢ A)
            --------------------------------
          → renˢ ρ M ≡ renˢ ρ' M
renˢ-cong p (` x) = cong ` (p x)
renˢ-cong p (ƛ M) = cong ƛ (renˢ-cong (extˢ-cong p) M)
renˢ-cong p (L · M) = cong₂ _·_ (renˢ-cong p L) (renˢ-cong p M)
renˢ-cong p (Λ M) = cong Λ (renˢ-cong (extˢ⋆-cong p) M)
renˢ-cong p (M ·⋆ A / q) = cong (_·⋆ A / q) (renˢ-cong p M)
renˢ-cong p (wrap A B M) = cong (wrap A B) (renˢ-cong p M)
renˢ-cong p (unwrap M q) = cong (λ M → unwrap M q) (renˢ-cong p M)
renˢ-cong p (con c) = refl
renˢ-cong p (builtin b / q) = refl
renˢ-cong p (error _) = refl

renˢ-id : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}(M : Γ ⊢ A)
  → renˢ id M ≡ M
renˢ-id (` x) = refl
renˢ-id (ƛ M) = cong ƛ (trans (renˢ-cong extˢ-id M) (renˢ-id M))
renˢ-id (L · M) = cong₂ _·_ (renˢ-id L) (renˢ-id M)
renˢ-id (Λ M) = cong Λ (trans (renˢ-cong extˢ⋆-id M) (renˢ-id M))
renˢ-id (M ·⋆ A / p) = cong (_·⋆ A / p) (renˢ-id M)
renˢ-id (wrap A B M) = cong (wrap A B) (renˢ-id M)
renˢ-id (unwrap M p) = cong (λ M → unwrap M p) (renˢ-id M)
renˢ-id (con c) = refl
renˢ-id (builtin b / p) = refl
renˢ-id (error _) = refl

renˢ-comp : ∀ {Φ Γ Δ Θ}{A : Φ ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(M : Γ ⊢ A)
  → renˢ (ρ ∘ ρ') M ≡ renˢ ρ (renˢ ρ' M)
renˢ-comp (` x) = refl
renˢ-comp (ƛ M) = cong ƛ (trans (renˢ-cong extˢ-comp M) (renˢ-comp M))
renˢ-comp (L · M) = cong₂ _·_ (renˢ-comp L) (renˢ-comp M)
renˢ-comp (Λ M) = cong Λ (trans (renˢ-cong extˢ⋆-comp M) (renˢ-comp M))
renˢ-comp (M ·⋆ A / p) = cong (_·⋆ A / p) (renˢ-comp M)
renˢ-comp (wrap A B M) = cong (wrap A B) (renˢ-comp M)
renˢ-comp (unwrap M p) = cong (λ M → unwrap M p) (renˢ-comp M)
renˢ-comp (con c) = refl
renˢ-comp (builtin b / p) = refl
renˢ-comp (error _) = refl


Subˢ : ∀{Φ} → Ctx Φ → Ctx Φ → Set
Subˢ Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

extsˢ : ∀ {Φ Γ Δ}
  → (σ : Subˢ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    ---------------------------------
  → Subˢ (Γ , B) (Δ , B)
extsˢ σ Z     = ` Z
extsˢ σ (S α) = weakenˢ (σ α)

-- cannot define this using renˢ
{-
exts⋆ˢ : ∀{Φ}{Γ Δ : Ctx Φ}
  → (σ : Subˢ Γ Δ)
  → ∀ {K}
    ----------------------
  → Subˢ (Γ ,⋆ K) (Δ ,⋆ K)
-}
\end{code}
