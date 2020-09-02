\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
import Data.Product as P
open import Relation.Binary.PropositionalEquality
open import Function hiding (_∋_)
open import Data.List using (List;[];_∷_)
open import Data.Vec using (Vec;[];_∷_;_++_)

open import Utils
open import Type
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic as A
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Untyped
import Untyped.RenamingSubstitution as U
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AB
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
  as AS
\end{code}

\begin{code}
backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → Fin (len Γ) → Φ ⊢Nf⋆ *
backVar⋆ (Γ ,⋆ J) x       = weakenNf (backVar⋆ Γ x)
backVar⋆ (Γ , A)  zero    = A
backVar⋆ (Γ , A)  (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(i : Fin (len Γ)) → Γ ∋ (backVar⋆ Γ i)
backVar (Γ ,⋆ J) x      = T (backVar Γ x)
backVar (Γ , A) zero    = Z
backVar (Γ , A) (suc x) = S (backVar Γ x)

backVar⋆-eraseVar : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A) →
  backVar⋆ Γ (eraseVar x) ≡ A
backVar⋆-eraseVar (Z) = refl
backVar⋆-eraseVar (S x) = backVar⋆-eraseVar x
backVar⋆-eraseVar (T x) = cong weakenNf (backVar⋆-eraseVar x)

subst-S : ∀{Φ}{Γ : Ctx Φ}{B A A' : Φ ⊢Nf⋆ *}(p : A ≡ A')(x : Γ ∋ A) →
  conv∋ refl p (S {B = B} x) ≡ S (conv∋ refl p x)
subst-S refl x = refl

subst-T : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}{K} →
  (p : A ≡ A')(q : weakenNf {K = K} A ≡ weakenNf A') → (x : Γ ∋ A) →
  conv∋ refl q (T x) ≡ T (conv∋ refl p x) -- 
subst-T refl refl x = refl

subst-T' : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}{K}{A'' : Φ ,⋆ K ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (q : weakenNf {K = K} A ≡ A'')
  → (r : weakenNf  {K = K} A' ≡ A'')
  → (x : Γ ∋ A) →
  conv∋ refl q (T x) ≡ conv∋ refl r (T (conv∋ refl p x))
subst-T' refl refl refl x = refl

cong-erase-ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋ A)(x' : Γ ∋ A') → conv∋ refl p x' ≡ x
  → eraseVar (ρ x) ≡ eraseVar (ρ x')
cong-erase-ren ρ⋆ ρ refl x .x refl = refl

backVar-eraseVar : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A) →
  conv∋ refl (backVar⋆-eraseVar x) (backVar Γ (eraseVar x)) ≡ x
backVar-eraseVar Z = refl
backVar-eraseVar (S x) = trans
  (subst-S (backVar⋆-eraseVar x) (backVar _ (eraseVar x)))
  (cong S (backVar-eraseVar x))
backVar-eraseVar (T x) = trans (subst-T (backVar⋆-eraseVar x) (cong weakenNf (backVar⋆-eraseVar x)) (backVar _ (eraseVar x))) (cong T (backVar-eraseVar x))

eraseVar-backVar : ∀{Φ}(Γ : Ctx Φ)(x : Fin (len Γ)) →
  eraseVar (backVar Γ x) ≡ x
eraseVar-backVar ∅        ()
eraseVar-backVar (Γ ,⋆ J) x      = eraseVar-backVar Γ x
eraseVar-backVar (Γ , A) zero    = refl
eraseVar-backVar (Γ , A) (suc x) = cong suc (eraseVar-backVar Γ x)

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
  → eraseVar (conv∋ refl p x) ≡ eraseVar x
conv∋-erase refl x = refl

conv⊢-erase : ∀{Φ}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (t : Γ ⊢ A)
  → erase (conv⊢ refl p t) ≡ erase t
conv⊢-erase refl t = refl

renTermCon-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){tc : TyCon}(c : AB.TermCon (con tc))
  → eraseTC {Γ = Δ} (A.renTermCon ρ⋆ c) ≡ eraseTC {Γ = Γ} c 
renTermCon-erase ρ⋆ ρ (AB.integer i)    = refl
renTermCon-erase ρ⋆ ρ (AB.bytestring b) = refl
renTermCon-erase ρ⋆ ρ (AB.string s)     = refl
renTermCon-erase ρ⋆ ρ (AB.bool b)       = refl
renTermCon-erase ρ⋆ ρ (AB.char c)       = refl
renTermCon-erase ρ⋆ ρ AB.unit           = refl

ext⋆-erase : ∀{Φ Ψ K}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)(α : Fin (len Γ))
  → erase-Ren (⋆.ext ρ⋆ {K = K}) (A.ext⋆ ρ⋆ ρ) α ≡ erase-Ren ρ⋆ ρ α
ext⋆-erase {Γ = Γ} ρ⋆ ρ α = conv∋-erase
  (trans (sym (renNf-comp (backVar⋆ Γ α))) (renNf-comp (backVar⋆ Γ α)))
  (T (ρ (backVar Γ α)))

renTel⋆-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)
  → ∀ Φ'
  → U.renTel (erase-Ren ρ⋆ ρ) (eraseTel⋆ Γ Φ') ≡ eraseTel⋆ Δ Φ'
renTel⋆-erase ρ⋆ ρ ∅        = refl
renTel⋆-erase {Γ = Γ} ρ⋆ ρ (Φ' ,⋆ K) = trans
  (U.renTel:< (erase-Ren ρ⋆ ρ) (eraseTel⋆ Γ Φ') (con unit))
  (cong (_:< _) (renTel⋆-erase ρ⋆ ρ Φ'))

ren-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.ren ρ⋆ ρ t) ≡ U.ren (erase-Ren ρ⋆ ρ) (erase t)

renTel-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)
  → ∀ Φ'
  → (As : List (Φ' ⊢Nf⋆ *))
  → (σ : SubNf Φ' Φ)
  → (tel : A.Tel Γ Φ' σ As)
  → eraseTel (A.renTel ρ⋆ ρ tel) ≡ U.renTel (erase-Ren ρ⋆ ρ) (eraseTel tel)

renTel'-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)
  → ∀ Φ'
  → (As : List (Φ' ⊢Nf⋆ *))
  → (σ : SubNf Φ' Φ)
  → (tel : A.Tel Γ Φ' σ As)
  → eraseTel⋆ Δ Φ' ++ eraseTel (A.renTel ρ⋆ ρ tel)
    ≡
    U.renTel (erase-Ren ρ⋆ ρ) (eraseTel⋆ Γ Φ' ++ eraseTel tel)
renTel'-erase {Γ = Γ} ρ⋆ ρ Φ' As σ ts = trans
  (cong₂ _++_
    (sym (renTel⋆-erase ρ⋆ ρ Φ'))
    (renTel-erase {Γ = Γ} ρ⋆ ρ Φ' As σ ts) )
  (sym (U.renTel++ (erase-Ren ρ⋆ ρ) (eraseTel⋆ Γ Φ') (eraseTel ts)))
renTel-erase ρ⋆ ρ Φ' []       σ tel = refl
renTel-erase ρ⋆ ρ Φ' (A ∷ As) σ (t ∷ tel) = cong₂ _∷_
  (trans (conv⊢-erase (sym (renNf-substNf σ ρ⋆ A)) (A.ren ρ⋆ ρ t))
         (ren-erase ρ⋆ ρ t))
  (renTel-erase ρ⋆ ρ Φ' As σ tel)

ren-erase ρ⋆ ρ (` x) = cong
  `
  (cong-erase-ren
    ρ⋆
    ρ
    (backVar⋆-eraseVar x)
    x
    (backVar _ (eraseVar x))
    (backVar-eraseVar x))
ren-erase ρ⋆ ρ (ƛ t)            = cong ƛ
  (trans
    (ren-erase ρ⋆ (A.ext ρ⋆ ρ) t)
    (U.ren-cong (ext-erase ρ⋆ ρ) (erase t)))
ren-erase ρ⋆ ρ (t · u)            =
  cong₂ _·_ (ren-erase ρ⋆ ρ t) (ren-erase ρ⋆ ρ u)
ren-erase ρ⋆ ρ (Λ t)            = cong ƛ (trans (trans (cong U.weaken (ren-erase (⋆.ext ρ⋆) (A.ext⋆ ρ⋆ ρ) t)) (trans (sym (U.ren-comp (erase-Ren (⋆.ext ρ⋆) (A.ext⋆ ρ⋆ ρ)) suc (erase t))) (U.ren-cong (cong suc ∘ ext⋆-erase ρ⋆ ρ) (erase t)))) (U.ren-comp suc (U.lift (erase-Ren ρ⋆ ρ)) (erase t)))
ren-erase ρ⋆ ρ (_·⋆_ {B = B} t A) = trans
  (conv⊢-erase (sym (ren[]Nf ρ⋆ B A)) (A.ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A)) (cong (_· plc_dummy) (ren-erase ρ⋆ ρ t))
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
  (cong (builtin bn (lemma≤ bn)) (renTel'-erase ρ⋆ ρ Φ As σ tel ))
ren-erase ρ⋆ ρ (error A)          = refl
--

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → A.Sub σ⋆ Γ Δ → U.Sub (len Γ) (len Δ) 
erase-Sub σ⋆ σ i = erase (σ (backVar _ i))

cong-erase-sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋ A)(x' : Γ ∋ A') → conv∋ refl p x' ≡ x
  → erase (σ x) ≡ erase (σ x')
cong-erase-sub σ⋆ σ refl x .x refl = refl

exts-erase : ∀ {Φ Ψ}{Γ Δ}(σ⋆ : SubNf Φ Ψ)(σ : A.Sub σ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
  → (α : Fin (suc (len Γ)))
  → erase-Sub σ⋆ (A.exts σ⋆ σ {B}) α ≡ U.lifts (erase-Sub σ⋆ σ) α
exts-erase σ⋆ σ zero = refl
exts-erase {Γ = Γ}{Δ} σ⋆ σ {B} (suc α) = trans
  (conv⊢-erase
    (renNf-id (substNf σ⋆ (backVar⋆ Γ α)))
    (A.ren id (conv∋ refl (sym (renNf-id _)) ∘ S) (σ (backVar Γ α))))
    (trans (ren-erase id (conv∋ refl (sym (renNf-id _)) ∘ S) (σ (backVar Γ α)))
           (U.ren-cong (λ β → trans
             (conv∋-erase (sym (renNf-id _)) (S (backVar Δ β)))
             (cong suc (eraseVar-backVar Δ β)))
             (erase (σ (backVar Γ α)))))

exts⋆-erase : ∀ {Φ Ψ}{Γ Δ}(σ⋆ : SubNf Φ Ψ)(σ : A.Sub σ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
  → ∀{K}
  → (α : Fin (len Γ))
  →  erase-Sub (extsNf σ⋆ {K}) (A.exts⋆ σ⋆ σ) α ≡ erase-Sub σ⋆ σ α 
exts⋆-erase {Γ = Γ}{Δ} σ⋆ σ {B} α = trans
  (conv⊢-erase
    (weakenNf-substNf σ⋆ (backVar⋆ Γ α))
    (A.weaken⋆ (σ (backVar Γ α))))
  (trans
    (ren-erase S T (σ (backVar Γ α)))
    (trans
      (U.ren-cong (eraseVar-backVar Δ) (erase (σ (backVar Γ α))))
      (sym (U.ren-id (erase (σ (backVar Γ α)))))))

subTermCon-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){tc : TyCon}(c : AB.TermCon (con tc))
  → eraseTC {Γ = Δ} (A.substTermCon σ⋆ c) ≡ eraseTC {Γ = Γ} c 
subTermCon-erase σ⋆ σ (AB.integer i)    = refl
subTermCon-erase σ⋆ σ (AB.bytestring b) = refl
subTermCon-erase σ⋆ σ (AB.string s)     = refl
subTermCon-erase σ⋆ σ (AB.bool b)       = refl
subTermCon-erase σ⋆ σ (AB.char c)       = refl
subTermCon-erase σ⋆ σ AB.unit           = refl

subTel⋆-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ)
  → ∀ Φ'
  → U.subTel (erase-Sub σ⋆ σ) (eraseTel⋆ Γ Φ') ≡ eraseTel⋆ Δ Φ'
subTel⋆-erase σ⋆ σ ∅        = refl
subTel⋆-erase {Γ = Γ} σ⋆ σ (Φ' ,⋆ K) = trans
  (U.subTel:< (erase-Sub σ⋆ σ) (eraseTel⋆ Γ Φ') (con unit))
  (cong (_:< _) (subTel⋆-erase σ⋆ σ Φ'))

sub-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.subst σ⋆ σ t) ≡ U.sub (erase-Sub σ⋆ σ) (erase t) 

subTel-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ)
  → ∀ Φ'
  → (As : List (Φ' ⊢Nf⋆ *))
  → (σ' : SubNf Φ' Φ)
  → (tel : A.Tel Γ Φ' σ' As)
  →  eraseTel (A.substTel σ⋆ σ tel) ≡ U.subTel (erase-Sub σ⋆ σ) (eraseTel tel) 
subTel-erase σ⋆ σ Φ' []       σ' tel = refl
subTel-erase σ⋆ σ Φ' (A ∷ As) σ' (t ∷ tel) = cong₂ _∷_
  (trans
    (conv⊢-erase (sym (substNf-comp σ' σ⋆ A)) (A.subst σ⋆ σ t))
    (sub-erase σ⋆ σ t))
  (subTel-erase σ⋆ σ Φ' As σ' tel)

subTel'-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ)
  → ∀ Φ'
  → (As : List (Φ' ⊢Nf⋆ *))
  → (σ' : SubNf Φ' Φ)
  → (tel : A.Tel Γ Φ' σ' As)
  → eraseTel⋆ Δ Φ' ++ eraseTel (A.substTel σ⋆ σ tel)
    ≡
    U.subTel (erase-Sub σ⋆ σ) (eraseTel⋆ Γ Φ' ++ eraseTel tel)
subTel'-erase {Γ = Γ} ρ⋆ ρ Φ' As σ ts = trans
  (cong₂ _++_
    (sym (subTel⋆-erase ρ⋆ ρ Φ'))
    (subTel-erase {Γ = Γ} ρ⋆ ρ Φ' As σ ts) )
  (sym (U.subTel++ (erase-Sub ρ⋆ ρ) (eraseTel⋆ Γ Φ') (eraseTel ts)))

sub-erase σ⋆ σ (` x) =   cong-erase-sub
    σ⋆
    σ
    (backVar⋆-eraseVar x)
    x
    (backVar _ (eraseVar x))
    (backVar-eraseVar x)
sub-erase σ⋆ σ (ƛ t) = cong ƛ
  (trans (sub-erase σ⋆ (A.exts σ⋆ σ) t)
         (U.sub-cong (exts-erase σ⋆ σ) (erase t)))
sub-erase σ⋆ σ (t · u) = cong₂ _·_ (sub-erase σ⋆ σ t) (sub-erase σ⋆ σ u)
sub-erase σ⋆ σ (Λ {B = B} t) = cong ƛ (trans
  (cong U.weaken (conv⊢-erase (subst-nf-Π σ⋆ B) (A.subst (extsNf σ⋆) (A.exts⋆ σ⋆ σ) t)))
  (trans (cong U.weaken (sub-erase (extsNf σ⋆) (A.exts⋆ σ⋆ σ) t))
         (trans (trans (sym (U.ren-sub (erase-Sub (extsNf σ⋆) (A.exts⋆ σ⋆ σ)) suc (erase t)))
                       (U.sub-cong (λ x → cong U.weaken (exts⋆-erase σ⋆ σ {B = Π B} x)) (erase t)))
                (U.sub-ren suc (U.lifts (erase-Sub σ⋆ σ)) (erase t)))))
sub-erase σ⋆ σ (_·⋆_ {B = B} t A) = trans
  (conv⊢-erase (sym (subst[]Nf' σ⋆ A B)) (A.subst σ⋆ σ t ·⋆ substNf σ⋆ A)) (cong (_· plc_dummy) (sub-erase σ⋆ σ t))
sub-erase σ⋆ σ (wrap1 pat arg t) = trans
  (conv⊢-erase (subst-nf-μ σ⋆ pat arg) (A.subst σ⋆ σ t))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (unwrap1 {pat = pat}{arg} t) = trans
  (conv⊢-erase (sym (subst-nf-μ σ⋆ pat arg)) (unwrap1 (A.subst σ⋆ σ t)))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (con c) = cong con (subTermCon-erase σ⋆ σ c)
sub-erase σ⋆ σ (builtin bn σ' tel) = let Φ P., As P., X = SIG bn in trans
  (conv⊢-erase
    (substNf-comp σ' σ⋆ X)
    (builtin bn (substNf σ⋆ ∘ σ') (A.substTel σ⋆ σ tel)))
  (cong (builtin bn (lemma≤ bn)) (subTel'-erase σ⋆ σ Φ As σ' tel))
sub-erase σ⋆ σ (error A) = refl

lem[]⋆ : ∀{Φ}{Γ : Ctx Φ}{K}{B : Φ ,⋆ K ⊢Nf⋆ *}(N : Γ ,⋆ K ⊢ B)(A : Φ ⊢Nf⋆ K)
  → erase N ≡ erase (N A.[ A ]⋆)
lem[]⋆ {Γ = Γ} N A = trans
  (trans
    (U.sub-id (erase N))
    (U.sub-cong
      (λ α → trans
        (cong ` (sym (eraseVar-backVar Γ α)))
        (sym (conv⊢-erase (weakenNf[] _ _) (` (backVar Γ α)))))
      (erase N)))
  (sym (sub-erase (substNf-cons (ne ∘ `) A) A.lem N)) 

open import Type.BetaNBE
open import Type.BetaNBE.Stability

lem[] : ∀{Φ}{Γ : Ctx Φ}{A B : Φ ⊢Nf⋆ *}(N : Γ , A ⊢ B)(W : Γ ⊢ A)
  → erase N U.[ erase W ] ≡ erase (N A.[ W ])
lem[] {Γ = Γ}{A = A}{B} N W = trans
  (trans
    (U.sub-cong
      (λ{ zero    → sym (conv⊢-erase (sym (substNf-id A)) W)
        ; (suc α) → trans
               (cong ` (sym (eraseVar-backVar Γ α)))
               (sym (conv⊢-erase (sym (substNf-id (backVar⋆ Γ α))) (` (backVar Γ α))))})
      (erase N))
    (sym (sub-erase (ne ∘ `) (A.substcons (ne ∘ `) (conv⊢ refl (sym (substNf-id _)) ∘ `) (conv⊢ refl (sym (substNf-id A)) W)) N)))
  (sym
    (conv⊢-erase
      (substNf-id B)
      (A.subst (ne ∘ `)
         (A.substcons
           (ne ∘ `)
           (conv⊢ refl (sym (substNf-id _)) ∘ `)
           (conv⊢ refl (sym (substNf-id A)) W))
         N)))
\end{code}
