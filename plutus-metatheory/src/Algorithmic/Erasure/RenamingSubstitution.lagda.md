---)
title: Algorithmic.Erasure.RenamingSubstitution
layout: page
---
```
module Algorithmic.Erasure.RenamingSubstitution where
```

```
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;subst;cong;cong₂)
open import Function using (id;_∘_)
open import Data.Vec using (Vec;_∷_;lookup)
open import Data.Fin using (Fin;toℕ;suc;zero)
open import Data.Nat using (ℕ;suc;zero)

open import Utils using (Kind;*;Maybe;nothing;just)
open import Utils.List using (List;[];_∷_)
open import Type using (Ctx⋆;∅;_,⋆_;_∋⋆_;Z;S)
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;weakenNf;renNf;lookup-renNf-VecList;embNf;embNf-VecList;lookup-embNf-VecList)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (lookup-eval-VecList;idEnv)
open import Type.BetaNormal.Equality using (renNf-id;renNf-comp)
open import Type.BetaNBE.RenamingSubstitution
                using (ren[]Nf;ren-nf-μ;SubNf;subNf-id;subNf;weakenNf[];weakenNf-subNf)
                using (sub-nf-Π;sub[]Nf';sub-nf-μ;subNf-cons;extsNf)
open import Algorithmic as A using (Ctx;_∋_;conv∋;_⊢_;conv⊢;Cases;[];_∷_)
open import Algorithmic.Signature using (btype-ren;btype-sub)
open Ctx
open _∋_
open _⊢_
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure using (len;erase;eraseTC;eraseVar;lem-erase;erase-Cases;erase-ConstrArgs;lem-erase'')
open import Untyped using (_⊢)
open _⊢
import Untyped.RenamingSubstitution as U
open import Builtin.Constant.Type using (TyCon)
```

```
backVar⋆ : ∀{Φ}(Γ : Ctx Φ) → Fin (len Γ) → Φ ⊢Nf⋆ *
backVar⋆ (Γ ,⋆ J) x        = weakenNf (backVar⋆ Γ x)
backVar⋆ (Γ , A)  zero  = A
backVar⋆ (Γ , A)  (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : Ctx Φ)(x : Fin (len Γ)) → Γ ∋ (backVar⋆ Γ x)
backVar (Γ ,⋆ J) x       = T (backVar Γ x)
backVar (Γ , A) zero  = Z
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
  → (x : Γ ∋ A)
  → conv∋ refl q (T x) ≡ conv∋ refl r (T (conv∋ refl p x))
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

eraseVar-backVar : ∀{Φ}(Γ : Ctx Φ)(x : Fin (len Γ)) → eraseVar (backVar Γ x) ≡ x
eraseVar-backVar ∅       ()
eraseVar-backVar (Γ ,⋆ J) x        = eraseVar-backVar Γ x
eraseVar-backVar (Γ , A)  zero  = refl
eraseVar-backVar (Γ , A)  (suc x) = cong suc (eraseVar-backVar Γ x)

--

erase-Ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → A.Ren ρ⋆ Γ Δ → U.Ren (len Γ) (len Δ)
erase-Ren ρ⋆ ρ i = eraseVar (ρ (backVar _ i))

ext-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *}(α : Fin (len (Γ , A)))
  → erase-Ren ρ⋆ (A.ext ρ⋆ ρ {B = A}) α ≡ U.lift (erase-Ren ρ⋆ ρ) α
ext-erase ρ⋆ ρ zero  = refl
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

ext⋆-erase : ∀{Φ Ψ K}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)(α : Fin (len Γ))
  → erase-Ren (⋆.ext ρ⋆ {K = K}) (A.ext⋆ ρ⋆ ρ) α ≡ erase-Ren ρ⋆ ρ α
ext⋆-erase {Γ = Γ} ρ⋆ ρ α = conv∋-erase
  (trans (sym (renNf-comp (backVar⋆ Γ α))) (renNf-comp (backVar⋆ Γ α)))
  (T (ρ (backVar Γ α)))

ren-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.ren ρ⋆ ρ t) ≡ U.ren (erase-Ren ρ⋆ ρ) (erase t)

ren-erase-ConstrArgs-List : ∀ {Φ} {Ψ} {Γ : Ctx Φ} {Δ : Ctx Ψ}
                              (ρ⋆ : ⋆.Ren Φ Ψ) (ρ : A.Ren ρ⋆ Γ Δ)
                              {As : List (Φ ⊢Nf⋆ *)}
                              (cs : A.ConstrArgs Γ As) →
                            erase-ConstrArgs ((A.ren-ConstrArgs-List ρ⋆ ρ cs)) ≡
                            U.renList (erase-Ren ρ⋆ ρ) (erase-ConstrArgs cs)
ren-erase-ConstrArgs-List ρ⋆ ρ [] = refl
ren-erase-ConstrArgs-List ρ⋆ ρ (x ∷ cs) = cong₂ _∷_ (ren-erase ρ⋆ ρ x) (ren-erase-ConstrArgs-List ρ⋆ ρ cs)

ren-erase-ConstrArgs : ∀ {Φ} {Ψ} {Γ : Ctx Φ} {Δ : Ctx Ψ}
                         (ρ⋆ : ⋆.Ren Φ Ψ) (ρ : A.Ren ρ⋆ Γ Δ) {n} (i : Fin n)
                         (Tss : Vec (List (Φ ⊢Nf⋆ *)) n)
                         (cs : A.ConstrArgs Γ (lookup Tss i)) →
                       erase-ConstrArgs (A.ren-ConstrArgs ρ⋆ ρ i Tss cs)
                       ≡ U.renList (erase-Ren ρ⋆ ρ)(erase-ConstrArgs cs)
ren-erase-ConstrArgs ρ⋆ ρ i Tss cs rewrite lookup-renNf-VecList ρ⋆ i Tss = ren-erase-ConstrArgs-List ρ⋆ ρ cs

ren-erase-Cases : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : A.Ren ρ⋆ Γ Δ)
  → ∀ {n}{A : Φ ⊢Nf⋆ *}{Tss : Vec (List (Φ ⊢Nf⋆ *)) n}
  → (cs : Cases Γ A Tss)
  →  erase-Cases (A.ren-Cases ρ⋆ ρ cs) ≡ U.renList (erase-Ren ρ⋆ ρ) (erase-Cases cs)
ren-erase-Cases ρ⋆ ρ [] = refl
ren-erase-Cases ρ⋆ ρ {Tss = As ∷ _}(c ∷ cs) =
      cong₂ _∷_ (trans (sym (lem-erase'' (A.ren-mkCaseType ρ⋆ As) (A.ren ρ⋆ ρ c)))
                       (ren-erase ρ⋆ ρ c))
                (ren-erase-Cases ρ⋆ ρ cs)

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
ren-erase ρ⋆ ρ (Λ t)            = cong
  delay
  (trans (ren-erase (⋆.ext ρ⋆) (A.ext⋆ ρ⋆ ρ) t)
         (U.ren-cong (ext⋆-erase ρ⋆ ρ) (erase t)))
ren-erase ρ⋆ ρ (_·⋆_/_ {B = B} t A refl) = trans
  (conv⊢-erase (sym (ren[]Nf ρ⋆ B A)) (A.ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A / refl ))
  (cong force (ren-erase ρ⋆ ρ t))
ren-erase ρ⋆ ρ (wrap A B t)  = trans
  (conv⊢-erase (ren-nf-μ ρ⋆ A B) (A.ren ρ⋆ ρ t))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (unwrap {A = A}{B = B} t refl) = trans
  (conv⊢-erase (sym (ren-nf-μ ρ⋆ A B)) (unwrap (A.ren ρ⋆ ρ t) refl))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (con c refl)            = refl
ren-erase ρ⋆ ρ (builtin b / refl)      =
  sym (lem-erase refl (btype-ren b ρ⋆) (builtin b / refl))
ren-erase ρ⋆ ρ (constr i A refl cs) = cong (constr (toℕ i)) (ren-erase-ConstrArgs ρ⋆ ρ i A cs)
ren-erase ρ⋆ ρ (case t cases) = cong₂ case (ren-erase ρ⋆ ρ t) (ren-erase-Cases ρ⋆ ρ cases)
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
    (renNf-id (subNf σ⋆ (backVar⋆ Γ α)))
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
    (weakenNf-subNf σ⋆ (backVar⋆ Γ α))
    (A.weaken⋆ (σ (backVar Γ α))))
  (trans
    (ren-erase S T (σ (backVar Γ α)))
    (trans
      (U.ren-cong (eraseVar-backVar Δ) (erase (σ (backVar Γ α))))
      (sym (U.ren-id (erase (σ (backVar Γ α)))))))

sub-erase : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}(σ⋆ : SubNf Φ Ψ)
  → (σ : A.Sub σ⋆ Γ Δ){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢ A)
  →  erase (A.sub σ⋆ σ t) ≡ U.sub (erase-Sub σ⋆ σ) (erase t)


sub-Erase-ConstrList : ∀ {Φ}{Ψ}{Γ : Ctx Φ} {Δ : Ctx Ψ}
                         {As : List (Φ ⊢Nf⋆ *)}
                         (σ⋆ : SubNf Φ Ψ) (σ : A.Sub σ⋆ Γ Δ)
                         (cs : A.ConstrArgs Γ As)
       →   erase-ConstrArgs (A.sub-ConstrList σ⋆ σ cs)
         ≡ U.subList (λ i₁ → erase (σ (backVar Γ i₁))) (erase-ConstrArgs cs)
sub-Erase-ConstrList σ⋆ σ [] = refl
sub-Erase-ConstrList σ⋆ σ (x ∷ cs) = cong₂ _∷_ (sub-erase σ⋆ σ x) (sub-Erase-ConstrList σ⋆ σ cs)

sub-Erase-ConstrArgs : ∀ {Φ} {Ψ} {Γ : Ctx Φ} {Δ : Ctx Ψ}
                         (σ⋆ : SubNf Φ Ψ) (σ : A.Sub σ⋆ Γ Δ) {n} (i : Fin n)
                         (Tss : Vec (List (Φ ⊢Nf⋆ *)) n)
                         (cs : A.ConstrArgs Γ (lookup Tss i))
                → erase-ConstrArgs (A.sub-VecList σ⋆ σ i Tss cs) ≡ U.subList (erase-Sub σ⋆ σ) (erase-ConstrArgs cs)
sub-Erase-ConstrArgs σ⋆ σ i Tss cs
     rewrite lookup-eval-VecList i (⋆.sub-VecList (λ x₁ → embNf (σ⋆ x₁)) (embNf-VecList Tss))
                                   (idEnv _)
            | ⋆.lookup-sub-VecList (λ x₁ → embNf (σ⋆ x₁)) i (embNf-VecList Tss)
            | lookup-embNf-VecList i Tss = sub-Erase-ConstrList σ⋆ σ cs

sub-erase-Cases : ∀ {Φ} {Ψ} {Γ : Ctx Φ} {Δ : Ctx Ψ}
                    (σ⋆ : SubNf Φ Ψ) (σ : A.Sub σ⋆ Γ Δ) {A : Φ ⊢Nf⋆ *} {n}
                    {Tss : Vec (List (Φ ⊢Nf⋆ *)) n}
                    (cases : Cases Γ A Tss) →
                  erase-Cases (A.sub-Cases σ⋆ σ cases) ≡
                  U.subList (erase-Sub σ⋆ σ) (erase-Cases cases)
sub-erase-Cases σ⋆ σ [] = refl
sub-erase-Cases {Δ = Δ} σ⋆ σ {Tss = As ∷ _} (c ∷ cases) = cong₂ _∷_ (trans (sym (lem-erase'' (A.sub-mkCaseType σ⋆ As) (A.sub σ⋆ σ c))) (sub-erase σ⋆ σ c))
                                             (sub-erase-Cases σ⋆ σ cases)

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
sub-erase σ⋆ σ (Λ {B = B} t) = cong
  delay
  (trans (conv⊢-erase (sub-nf-Π σ⋆ B) (A.sub (extsNf σ⋆) (A.exts⋆ σ⋆ σ) t))
         (trans (sub-erase (extsNf σ⋆) (A.exts⋆ σ⋆ σ) t)
                (U.sub-cong (exts⋆-erase σ⋆ σ {B = Π B}) (erase t))))
sub-erase σ⋆ σ (_·⋆_/_ {B = B} t A refl) =
  trans (conv⊢-erase (sym (sub[]Nf' σ⋆ A B)) (A.sub σ⋆ σ t ·⋆ subNf σ⋆ A / refl))
        (cong force (sub-erase σ⋆ σ t))
sub-erase σ⋆ σ (wrap A B t) = trans
  (conv⊢-erase (sub-nf-μ σ⋆ A B) (A.sub σ⋆ σ t))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (unwrap {A = A}{B} t refl) = trans
  (conv⊢-erase (sym (sub-nf-μ σ⋆ A B)) (unwrap (A.sub σ⋆ σ t) refl))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (con c refl) = refl
sub-erase σ⋆ σ (builtin b / refl) =
 sym (lem-erase refl (btype-sub b σ⋆) (builtin b / refl))
sub-erase σ⋆ σ (constr i A refl cs) = cong (constr (toℕ i)) (sub-Erase-ConstrArgs σ⋆ σ i A cs)
sub-erase σ⋆ σ (case t cases) = cong₂ case (sub-erase σ⋆ σ t) (sub-erase-Cases σ⋆ σ cases)
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
  (sym (sub-erase (subNf-cons (ne ∘ `) A) A.lem N))


lem[] : ∀{Φ}{Γ : Ctx Φ}{A B : Φ ⊢Nf⋆ *}(N : Γ , A ⊢ B)(W : Γ ⊢ A)
  → erase N U.[ erase W ] ≡ erase (N A.[ W ])
lem[] {Γ = Γ}{A = A}{B} N W = trans
  (trans
    (U.sub-cong
      (λ{ zero    → sym (conv⊢-erase (sym (subNf-id A)) W)
        ; (suc α) → trans
               (cong ` (sym (eraseVar-backVar Γ α)))
               (sym (conv⊢-erase (sym (subNf-id (backVar⋆ Γ α))) (` (backVar Γ α))))})
      (erase N))
    (sym (sub-erase (ne ∘ `) (A.subcons (ne ∘ `) (conv⊢ refl (sym (subNf-id _)) ∘ `) (conv⊢ refl (sym (subNf-id A)) W)) N)))
  (sym
    (conv⊢-erase
      (subNf-id B)
      (A.sub (ne ∘ `)
         (A.subcons
           (ne ∘ `)
           (conv⊢ refl (sym (subNf-id _)) ∘ `)
           (conv⊢ refl (sym (subNf-id A)) W))
         N)))
```

