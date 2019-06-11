\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Untyped
import Untyped.RenamingSubstitution as U

open import Data.Nat
open import Data.Fin
import Data.Product as P
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∋_)
\end{code}

\begin{code}
backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → Fin (len Γ) → Φ ⊢Nf⋆ *
backVar⋆ (Γ ,⋆ J) x = weakenNf (backVar⋆ Γ x)
backVar⋆ (Γ , A) zero    = A
backVar⋆ (Γ , A) (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(i : Fin (len Γ)) → Γ ∋ (backVar⋆ Γ i)
backVar (Γ ,⋆ J) x      = T (backVar Γ x)
backVar (Γ , A) zero    = Z
backVar (Γ , A) (suc x) = S (backVar Γ x)

backVar⋆-eraseVar : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A) →
  backVar⋆ Γ (eraseVar x) ≡ A
backVar⋆-eraseVar Z = refl
backVar⋆-eraseVar (S x) = backVar⋆-eraseVar x
backVar⋆-eraseVar (T x) = cong weakenNf (backVar⋆-eraseVar x)

subst-S : ∀{Φ}{Γ : Ctx Φ}{B A A' : Φ ⊢Nf⋆ *}(p : A ≡ A')(x : Γ ∋ A) →
  conv∋ p (S {B = B} x) ≡ S (conv∋ p x)
subst-S refl x = refl

subst-T : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}{K} →
  (p : A ≡ A')(q : weakenNf {K = K} A ≡ weakenNf A') → (x : Γ ∋ A) →
  conv∋ q (T x) ≡ T (conv∋ p x) -- 
subst-T refl refl x = refl


subst-T' : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}{K}{A'' : Φ ,⋆ K ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (q : weakenNf {K = K} A ≡ A'')
  → (r : weakenNf  {K = K} A' ≡ A'')
  → (x : Γ ∋ A) →
  conv∋ q (T x) ≡ conv∋ r (T (conv∋ p x))
subst-T' refl refl refl x = refl

cong-erase-ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋ A)(x' : Γ ∋ A') → conv∋ p x' ≡ x
  → eraseVar (ρ x) ≡ eraseVar (ρ x')
cong-erase-ren ρ⋆ ρ refl x .x refl = refl


backVar-eraseVar : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A) →
  conv∋ (backVar⋆-eraseVar x) (backVar Γ (eraseVar x)) ≡ x
backVar-eraseVar Z = refl
backVar-eraseVar {Γ = Γ , A} (S x) = trans
  (subst-S (backVar⋆-eraseVar x) (backVar _ (eraseVar x)))
  (cong S (backVar-eraseVar x))
backVar-eraseVar (T x) = trans
  (subst-T (backVar⋆-eraseVar x)
           (cong weakenNf (backVar⋆-eraseVar x))
           (backVar _ (eraseVar x)))
  (cong T (backVar-eraseVar x))

--

erase-Ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → A.Ren ρ⋆ Γ Δ → U.Ren (len Γ) (len Δ) 
erase-Ren ρ⋆ ρ i = eraseVar (ρ (backVar _ i))

ext-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *}(α : Fin (len (Γ , A)))
  → erase-Ren ρ⋆ (A.ext ρ⋆ ρ {B = A}) α ≡ U.lift (erase-Ren ρ⋆ ρ) α
ext-erase ρ⋆ ρ zero    = refl
ext-erase ρ⋆ ρ (suc α) = refl

conv∋-erase : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}(x : Γ ∋ A)
  → (p : A ≡ A')
  → eraseVar (conv∋ p x) ≡ eraseVar x
conv∋-erase x refl = refl

ext⋆-erase : ∀{Φ Ψ K}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)(α : Fin (len Γ))
  → erase-Ren (⋆.ext ρ⋆ {K = K}) (A.ext⋆ ρ⋆ ρ) α ≡ erase-Ren ρ⋆ ρ α
ext⋆-erase {Γ = Γ} ρ⋆ ρ α = conv∋-erase
  (T (ρ (backVar Γ α)))
  (trans (sym (renNf-comp (backVar⋆ Γ α))) (renNf-comp (backVar⋆ Γ α)))

ren-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.ren ρ⋆ ρ t) ≡ U.ren (erase-Ren ρ⋆ ρ) (erase t)
ren-erase ρ⋆ ρ (` x) = cong `
 (cong-erase-ren
   ρ⋆
   ρ
   (backVar⋆-eraseVar x)
   x
   (backVar _ (eraseVar x))
   (backVar-eraseVar x))
ren-erase ρ⋆ ρ (ƛ x t)            = cong (ƛ x)
  (trans
    (ren-erase ρ⋆ (A.ext ρ⋆ ρ) t)
    (U.ren-cong (ext-erase ρ⋆ ρ) (erase t)))
ren-erase ρ⋆ ρ (t · u)            =
  cong₂ _·_ (ren-erase ρ⋆ ρ t) (ren-erase ρ⋆ ρ u)
ren-erase ρ⋆ ρ (Λ x t)            = trans
  (ren-erase (⋆.ext ρ⋆) (A.ext⋆ ρ⋆ ρ) t)
  (U.ren-cong (ext⋆-erase ρ⋆ ρ) (erase t))
ren-erase ρ⋆ ρ (t ·⋆ A)           = trans {!!} (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (wrap1 pat arg t)  = trans {!!} (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (unwrap1 t)        = trans {!!} (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (con c)            = {!!}
ren-erase ρ⋆ ρ (builtin bn σ tel) = {!!}
ren-erase ρ⋆ ρ (error A)          = refl

--

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → A.Sub σ⋆ Γ Δ → U.Sub (len Γ) (len Δ) 
erase-Sub σ⋆ σ i = erase (σ (backVar _ i))

cong-erase-sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋ A)(x' : Γ ∋ A') → conv∋ p x' ≡ x
  → erase (σ x) ≡ erase (σ x')
cong-erase-sub σ⋆ σ refl x .x refl = refl

lifts-erase : ∀ {Φ Ψ}{Γ Δ}{σ⋆ : SubNf Φ Ψ}(σ : A.Sub σ⋆ Γ Δ)
  → (α : Fin (suc (len Γ)))
  → {B : Φ ⊢Nf⋆ *}
  → erase-Sub σ⋆ (A.exts σ⋆ σ {B}) α ≡ U.lifts (erase-Sub σ⋆ σ) α
lifts-erase σ zero = refl
lifts-erase σ (suc α) = {!!}

sub-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.subst σ⋆ σ t) ≡ U.sub (erase-Sub σ⋆ σ) (erase t) 
sub-erase σ⋆ σ (` x) =
  cong-erase-sub
    σ⋆
    σ
    (backVar⋆-eraseVar x)
    x
    (backVar _ (eraseVar x))
    (backVar-eraseVar x)
sub-erase σ⋆ σ (ƛ x t) = cong (ƛ x)
  (trans (sub-erase σ⋆ (A.exts σ⋆ σ) t)
         (U.sub-cong {!!} (erase t)))
sub-erase σ⋆ σ (t · u) = cong₂ _·_ (sub-erase σ⋆ σ t) (sub-erase σ⋆ σ u)
sub-erase σ⋆ σ (Λ x t) = {!sub-erase ? ? t!}
sub-erase σ⋆ σ (t ·⋆ A) = {!sub-erase σ⋆ σ t!}
sub-erase σ⋆ σ (wrap1 pat arg t) = {!sub-erase σ⋆ σ t!}
sub-erase σ⋆ σ (unwrap1 t) = {!!}
sub-erase σ⋆ σ (con x) = {!!}
sub-erase σ⋆ σ (builtin bn σ₁ ts) = {!!}
sub-erase σ⋆ σ (error A) = refl
  
lem[]⋆ : ∀{Φ}{Γ : Ctx Φ}{K}{B : Φ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{A : Φ ⊢Nf⋆ K}
  → erase N ≡ erase (N A.[ A ]⋆)
lem[]⋆ = {!!}

lem[] : ∀{Φ}{Γ : Ctx Φ}{A B : Φ ⊢Nf⋆ *}{N : Γ , A ⊢ B}{W : Γ ⊢ A}
  → erase N U.[ erase W ] ≡ erase (N A.[ W ])
lem[] = {!!}
\end{code}
