\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
import Data.Product as P
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∋_)
open import Data.List

open import Type
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Untyped
import Untyped.RenamingSubstitution as U
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AB
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf as AS
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

conv∋-erase : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (x : Γ ∋ A)
  → eraseVar (conv∋ p x) ≡ eraseVar x
conv∋-erase refl x = refl

conv⊢-erase : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (t : Γ ⊢ A)
  → erase (conv⊢ p t) ≡ erase t
conv⊢-erase refl t = refl

renTermCon-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){tc : TyCon}(c : AB.TermCon (con tc))
  → eraseTC {Γ = Δ} (A.renTermCon ρ⋆ c) ≡ eraseTC {Γ = Γ} c 
renTermCon-erase ρ⋆ ρ (AB.integer i)    = refl
renTermCon-erase ρ⋆ ρ (AB.bytestring b) = refl

ext⋆-erase : ∀{Φ Ψ K}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)(α : Fin (len Γ))
  → erase-Ren (⋆.ext ρ⋆ {K = K}) (A.ext⋆ ρ⋆ ρ) α ≡ erase-Ren ρ⋆ ρ α
ext⋆-erase {Γ = Γ} ρ⋆ ρ α = conv∋-erase
  (trans (sym (renNf-comp (backVar⋆ Γ α))) (renNf-comp (backVar⋆ Γ α)))
  (T (ρ (backVar Γ α)))

ren-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.ren ρ⋆ ρ t) ≡ U.ren (erase-Ren ρ⋆ ρ) (erase t)

renTel-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)
  → ∀ Φ'
  → (As : List (Φ' ⊢Nf⋆ *))
  → (σ : SubNf Φ' Φ)
  → (tel : Tel Γ Φ' σ As)
  → eraseTel (A.renTel ρ⋆ ρ tel) ≡ U.renList (erase-Ren ρ⋆ ρ) (eraseTel tel)

renTel-erase ρ⋆ ρ Φ' []       σ tel = refl
renTel-erase ρ⋆ ρ Φ' (A ∷ As) σ (t P., tel) = cong₂ _∷_
  (trans (conv⊢-erase (sym (renNf-substNf σ ρ⋆ A)) (A.ren ρ⋆ ρ t))
         (ren-erase ρ⋆ ρ t))
  (renTel-erase ρ⋆ ρ Φ' As σ tel)

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
ren-erase ρ⋆ ρ (_·⋆_ {B = B} t A) = trans
  (conv⊢-erase (sym (ren[]Nf ρ⋆ B A)) (A.ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (wrap1 pat arg t)  = trans
  (conv⊢-erase (ren-nf-μ1 ρ⋆ pat arg) (A.ren ρ⋆ ρ t))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (unwrap1 {pat = pat}{arg = arg} t) = trans
  (conv⊢-erase (sym (ren-nf-μ1 ρ⋆ pat arg)) (unwrap1 (A.ren ρ⋆ ρ t)))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (con c)            = cong con (renTermCon-erase ρ⋆ ρ c)
ren-erase ρ⋆ ρ (builtin bn σ tel) = let Φ P., As P., X = SIG bn in trans
  (conv⊢-erase
    (renNf-substNf σ ρ⋆ X)
    (builtin bn (renNf ρ⋆ ∘ σ) (A.renTel ρ⋆ ρ tel)))
  (cong (builtin bn) (renTel-erase ρ⋆ ρ Φ As σ tel))
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
lifts-erase σ (suc α) = {!erase!}

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
sub-erase σ⋆ σ (Λ x t) = {!!}
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
