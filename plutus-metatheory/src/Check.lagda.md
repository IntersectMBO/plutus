---
layout: page
---
## Type checker

```
module Check where
```

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong₂;cong;sym)
open import Relation.Nullary using (¬_)

open import Scoped using (ScopedTy;Weirdℕ;WeirdFin;ScopedTm)
open ScopedTy
open ScopedTm
open Weirdℕ
open WeirdFin

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;weakenNf;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Utils using (Kind;*;_⇒_;Either;inj₁;inj₂;withE;Monad;TermCon)
open Monad {{...}}
open TermCon

open import Type.Equality using (_≡β_;≡2β)
open _≡β_

open import Type.BetaNBE using (nf)
open import Type.BetaNBE.Soundness using (soundness)
open import Algorithmic using (_⊢_;Ctx;_∋_)
open import Algorithmic.Signature using (btype)
open _⊢_
open Ctx
open _∋_

open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) as T
import Builtin.Constant.Type ℕ ScopedTy as S
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as A
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ (i : Fin (len⋆ Φ)) → Σ Kind (Φ ∋⋆_)
inferTyVar (Φ ,⋆ K) zero    = K ,, Z
inferTyVar (Φ ,⋆ K) (suc i) = let J ,, α = inferTyVar Φ i in  J ,, S α

⊎bind : {A B C : Set} → A ⊎ C → (A → B ⊎ C) → B ⊎ C
⊎bind (inj₁ a) f = f a
⊎bind (inj₂ c) f = inj₂ c

data TypeError : Set where
  kindMismatch : (K K' : Kind) → ¬ (K ≡ K') → TypeError
  notStar : (K : Kind) → ¬ (K ≡ *) → TypeError
  notFunKind  : (K : Kind) → (∀ K' J → ¬ (K ≡ K' ⇒ J)) → TypeError
  notPat  : (K : Kind) → (∀ K' → ¬ (K ≡ (K' ⇒ *) ⇒ (K' ⇒ *))) → TypeError
  UnknownType : TypeError
  notPi  : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ,⋆ K ⊢Nf⋆ *) → ¬ (A ≡ Π A')) →
    TypeError
  notMu : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ⊢Nf⋆ _)(B : Φ ⊢Nf⋆ K) → ¬ (A ≡ μ A' B))
    → TypeError
  notFunType : ∀{Φ}(A : Φ ⊢Nf⋆ *) → ((A' B : Φ ⊢Nf⋆ *) → ¬ (A ≡ A' ⇒ B)) → TypeError
  typeMismatch : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → ¬ (A ≡ A') → TypeError
  builtinError : TypeError

meqKind : (K K' : Kind) → Either (¬ (K ≡ K')) (K ≡ K')
meqKind * * = inj₂ refl
meqKind * (K' ⇒ J') = inj₁ λ() 
meqKind (K ⇒ J) * = inj₁ λ()
meqKind (K ⇒ J) (K' ⇒ J') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q ← withE (λ ¬q → λ{refl → ¬q refl}) (meqKind J J')
  return (cong₂ _⇒_ p q)

isStar : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Φ ⊢Nf⋆ *)
isStar p = do
  * ,, A ← p
   where (K ⇒ J ,, _) → inj₁ (notStar (K ⇒ J) λ())
  return A

isFunKind : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Σ Kind λ J → Φ ⊢Nf⋆ K ⇒ J)
isFunKind p = do
  K ⇒ J ,, A ← p
    where (* ,, _) → inj₁ (notFunKind * λ _ _ ())
  return (K ,, J ,, A)

isPat : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *))
isPat p = do
  (K ⇒ *) ⇒ (K' ⇒ *) ,, A ← p
    where
      (* ,, _) → inj₁ (notPat * λ _ ())
      (K@(_ ⇒ *) ,, _) → inj₁ (notPat K λ _ ())
      (K@(_ ⇒ (_ ⇒ (_ ⇒ _))) ,, _) → inj₁ (notPat K λ _ ())
      (K@(* ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ (_ ⇒ _)) ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
  refl ← withE (kindMismatch _ _) (meqKind K K')
  return (K ,, A)

isPi :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ Kind λ K → Σ (Φ ,⋆ K ⊢Nf⋆ *) λ A → Γ ⊢ Π A)
isPi p = do
  Π A ,, L ← p
    where A ⇒ B ,, _ → inj₁ (notPi (A ⇒ B) (λ _ ()))
          ne A  ,, _ → inj₁ (notPi (ne A) (λ _ ()))
          con {Φ} c ,, _ → inj₁ (notPi (con {Φ} c) (λ _ ()))
          μ A B ,, _ → inj₁ (notPi (μ A B) (λ _ ()))
  return (_ ,, A ,, L)

isFunType :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Σ (Φ ⊢Nf⋆ *) λ B → Γ ⊢ A ⇒ B)
isFunType p = do
  A ⇒ B ,, L ← p
    where Π A ,, _ → inj₁ (notFunType (Π A) (λ _ _ ()))
          ne A  ,, _ → inj₁ (notFunType (ne A) (λ _ _ ()))
          con {Φ} c ,, _ → inj₁ (notFunType (con {Φ} c) (λ _ _ ()))
          μ A B ,, _ → inj₁ (notFunType (μ A B) (λ _ _ ()))
  return (A ,, B ,, L)
  
isMu :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ Kind λ K → Σ (Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *)) λ A → Σ (Φ ⊢Nf⋆ K) λ B → Γ ⊢ μ A B)
isMu p = do
  μ A B ,, L ← p
    where Π A ,, _ → inj₁ (notMu (Π A) (λ _ _ ()))
          ne A  ,, _ → inj₁ (notMu (ne A) (λ _ _ ()))
          con {Φ} c ,, _ → inj₁ (notMu (con {Φ} c) (λ _ _ ()))
          A ⇒ B ,, _ → inj₁ (notMu (A ⇒ B) (λ _ _ ()))
  return (_ ,, A ,, B ,, L)

checkKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → ∀ K → Either TypeError (Φ ⊢Nf⋆ K)
inferKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
inferKindCon : ∀ Φ (c : S.TyCon (len⋆ Φ)) → Either TypeError (T.TyCon Φ)

inferKindCon Φ S.integer = inj₂ T.integer
inferKindCon Φ S.bytestring = inj₂ T.bytestring
inferKindCon Φ S.string = inj₂ T.string
inferKindCon Φ S.unit = inj₂ T.unit
inferKindCon Φ S.bool = inj₂ T.bool
inferKindCon Φ (S.list A) = do
  A ← isStar (inferKind Φ A)
  return (T.list A)
inferKindCon Φ (S.pair A B) = do
  A ← isStar (inferKind Φ A)
  B ← isStar (inferKind Φ B)  
  return (T.pair A B)
inferKindCon Φ S.pdata = inj₂ T.pdata
inferKindCon Φ S.bls12-381-g1-element = inj₂ T.bls12-381-g1-element
inferKindCon Φ S.bls12-381-g2-element = inj₂ T.bls12-381-g2-element
inferKindCon Φ S.bls12-381-mlresult = inj₂ T.bls12-381-mlresult

checkKind Φ A K = do
  K' ,, A ← inferKind Φ A
  refl ← withE (kindMismatch _ _) (meqKind K K')
  return A

inferKind Φ (` α) = let K ,, β = inferTyVar Φ α in return (K ,, ne (` β))
inferKind Φ (A ⇒ B) = do
  A ← isStar (inferKind Φ A)
  B ← isStar (inferKind Φ B)
  return (* ,, A ⇒ B)
inferKind Φ (Π K A) = do
  A ← isStar (inferKind (Φ ,⋆ K) A)
  return (* ,, Π A)
inferKind Φ (ƛ K A) = do
  J ,, A ← inferKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ A)
inferKind Φ (A · B) = do
  (K ,, J ,, A) ← isFunKind (inferKind Φ A)
  B ← checkKind Φ B K
  return (J ,, nf (embNf A · embNf B))
inferKind Φ (con tc) = do
  tc ← inferKindCon Φ tc
  return (* ,, con tc)
inferKind Φ (μ A B) = do
  K ,, A ← isPat (inferKind Φ A)
  B ← checkKind Φ B K
  return (* ,, μ A B)
inferKind Φ missing = inj₁ UnknownType

len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ J) = Weirdℕ.T (len Γ)
len (Γ , A)  = Weirdℕ.S (len Γ)

inferVarType : ∀{Φ}(Γ : Ctx Φ) → WeirdFin (len Γ) 
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A)
inferVarType (Γ ,⋆ J) (WeirdFin.T x) = do
  A ,, α ← inferVarType Γ x
  return (weakenNf A ,, T α)
inferVarType (Γ , A) Z = return (A ,, Z)
inferVarType (Γ , A) (S x) = do
  A ,, α ← inferVarType Γ x
  return (A ,, S α)

meqTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → Either (¬ (α ≡ α')) (α ≡ α')
meqTyVar Z     Z      = inj₂ refl 
meqTyVar (S α) (S α') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyVar α α')
  return (cong S p)
meqTyVar Z     (S α') = inj₁ λ()
meqTyVar (S α) Z      = inj₁ λ()

meqNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → Either (¬ (A ≡ A')) (A ≡ A')
meqNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → Either (¬ (A ≡ A')) (A ≡ A')
meqTyCon : ∀{Φ}(c c' : T.TyCon Φ) → Either (¬ (c ≡ c')) (c ≡ c')

meqTyCon T.integer    T.integer    = inj₂ refl
meqTyCon T.bytestring T.bytestring = inj₂ refl
meqTyCon T.string     T.string     = inj₂ refl
meqTyCon T.bool       T.bool       = inj₂ refl
meqTyCon T.unit       T.unit       = inj₂ refl
meqTyCon T.pdata      T.pdata      = inj₂ refl
meqTyCon T.bls12-381-g1-element T.bls12-381-g1-element = inj₂ refl
meqTyCon T.bls12-381-g2-element T.bls12-381-g2-element = inj₂ refl
meqTyCon T.bls12-381-mlresult   T.bls12-381-mlresult   = inj₂ refl
meqTyCon (T.list A)   (T.list A')    = do
  refl ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
  return refl
meqTyCon (T.pair A B) (T.pair A' B') = do
  refl ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
  refl ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy B B')  
  return refl
--
meqTyCon T.integer    T.bytestring           = inj₁ λ()
meqTyCon T.integer    T.string               = inj₁ λ()
meqTyCon T.integer    T.bool                 = inj₁ λ()
meqTyCon T.integer    T.unit                 = inj₁ λ()
meqTyCon T.integer    T.pdata                = inj₁ λ()
meqTyCon T.integer    T.bls12-381-g1-element = inj₁ λ()
meqTyCon T.integer    T.bls12-381-g2-element = inj₁ λ()
meqTyCon T.integer    T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.integer    (T.list A)             = inj₁ λ()
meqTyCon T.integer    (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.bytestring T.integer              = inj₁ λ()
meqTyCon T.bytestring T.string               = inj₁ λ()
meqTyCon T.bytestring T.bool                 = inj₁ λ()
meqTyCon T.bytestring T.unit                 = inj₁ λ()
meqTyCon T.bytestring T.pdata                = inj₁ λ()
meqTyCon T.bytestring T.bls12-381-g1-element = inj₁ λ()
meqTyCon T.bytestring T.bls12-381-g2-element = inj₁ λ()
meqTyCon T.bytestring T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.bytestring (T.list A)             = inj₁ λ()
meqTyCon T.bytestring (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.string     T.integer              = inj₁ λ()
meqTyCon T.string     T.bytestring           = inj₁ λ()
meqTyCon T.string     T.bool                 = inj₁ λ()
meqTyCon T.string     T.unit                 = inj₁ λ()
meqTyCon T.string     T.pdata                = inj₁ λ()
meqTyCon T.string     T.bls12-381-g1-element = inj₁ λ()
meqTyCon T.string     T.bls12-381-g2-element = inj₁ λ()
meqTyCon T.string     T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.string     (T.list A)             = inj₁ λ()
meqTyCon T.string     (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.bool       T.integer              = inj₁ λ()
meqTyCon T.bool       T.bytestring           = inj₁ λ()
meqTyCon T.bool       T.string               = inj₁ λ()
meqTyCon T.bool       T.unit                 = inj₁ λ()
meqTyCon T.bool       T.pdata                = inj₁ λ()
meqTyCon T.bool       T.bls12-381-g1-element = inj₁ λ()
meqTyCon T.bool       T.bls12-381-g2-element = inj₁ λ()
meqTyCon T.bool       T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.bool       (T.list A)             = inj₁ λ()
meqTyCon T.bool       (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.unit      T.integer               = inj₁ λ()
meqTyCon T.unit      T.bytestring            = inj₁ λ()
meqTyCon T.unit      T.string                = inj₁ λ()
meqTyCon T.unit      T.bool                  = inj₁ λ()
meqTyCon T.unit      T.pdata                 = inj₁ λ()
meqTyCon T.unit      T.bls12-381-g1-element  = inj₁ λ()
meqTyCon T.unit      T.bls12-381-g2-element  = inj₁ λ()
meqTyCon T.unit      T.bls12-381-mlresult    = inj₁ λ()
meqTyCon T.unit      (T.list A)              = inj₁ λ()
meqTyCon T.unit      (T.pair A' B')          = inj₁ λ()
--
meqTyCon T.pdata     T.integer               = inj₁ λ()
meqTyCon T.pdata     T.bytestring            = inj₁ λ()
meqTyCon T.pdata     T.string                = inj₁ λ()
meqTyCon T.pdata     T.bool                  = inj₁ λ()
meqTyCon T.pdata     T.unit                  = inj₁ λ()
meqTyCon T.pdata     T.bls12-381-g1-element  = inj₁ λ()
meqTyCon T.pdata     T.bls12-381-g2-element  = inj₁ λ()
meqTyCon T.pdata     T.bls12-381-mlresult    = inj₁ λ()
meqTyCon T.pdata     (T.list A)              = inj₁ λ()
meqTyCon T.pdata     (T.pair A' B')          = inj₁ λ()
--
meqTyCon T.bls12-381-g1-element     T.integer              = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.string               = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.bytestring           = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.bool                 = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.unit                 = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.pdata                = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.bls12-381-g2-element = inj₁ λ()
meqTyCon T.bls12-381-g1-element     T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.bls12-381-g1-element     (T.list A)             = inj₁ λ()
meqTyCon T.bls12-381-g1-element     (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.bls12-381-g2-element     T.integer              = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.string               = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.bytestring           = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.bool                 = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.unit                 = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.pdata                = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.bls12-381-g1-element = inj₁ λ()
meqTyCon T.bls12-381-g2-element     T.bls12-381-mlresult   = inj₁ λ()
meqTyCon T.bls12-381-g2-element     (T.list A)             = inj₁ λ()
meqTyCon T.bls12-381-g2-element     (T.pair A' B')         = inj₁ λ()
--
meqTyCon T.bls12-381-mlresult   T.integer                  = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.string                   = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.bytestring               = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.bool                     = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.unit                     = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.pdata                    = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.bls12-381-g1-element     = inj₁ λ()
meqTyCon T.bls12-381-mlresult   T.bls12-381-g2-element     = inj₁ λ()
meqTyCon T.bls12-381-mlresult   (T.list A)                 = inj₁ λ()
meqTyCon T.bls12-381-mlresult   (T.pair A' B')             = inj₁ λ()
--
meqTyCon (T.list A)   T.integer              = inj₁ λ()
meqTyCon (T.list A)   T.string               = inj₁ λ()
meqTyCon (T.list A)   T.bytestring           = inj₁ λ()
meqTyCon (T.list A)   T.bool                 = inj₁ λ()
meqTyCon (T.list A)   T.unit                 = inj₁ λ()
meqTyCon (T.list A)   T.pdata                = inj₁ λ()
meqTyCon (T.list A)   T.bls12-381-g1-element = inj₁ λ()
meqTyCon (T.list A)   T.bls12-381-g2-element = inj₁ λ()
meqTyCon (T.list A)   T.bls12-381-mlresult   = inj₁ λ()
meqTyCon (T.list A)   (T.pair A' B')         = inj₁ λ()
--
meqTyCon (T.pair A B) T.integer              = inj₁ λ()
meqTyCon (T.pair A B) T.string               = inj₁ λ()
meqTyCon (T.pair A B) T.bytestring           = inj₁ λ()
meqTyCon (T.pair A B) T.bool                 = inj₁ λ()
meqTyCon (T.pair A B) T.unit                 = inj₁ λ()
meqTyCon (T.pair A B) T.pdata                = inj₁ λ()
meqTyCon (T.pair A B) T.bls12-381-g1-element = inj₁ λ()
meqTyCon (T.pair A B) T.bls12-381-g2-element = inj₁ λ()
meqTyCon (T.pair A B) T.bls12-381-mlresult   = inj₁ λ()
meqTyCon (T.pair A B) (T.list A')            = inj₁ λ()

meqNfTy (A ⇒ B) (A' ⇒ B') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNfTy A A')
  q ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy B B')
  return (cong₂ _⇒_ p q)
meqNfTy (ƛ A) (ƛ A') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNfTy A A')
  return (cong ƛ p)
meqNfTy (Π {K = K} A) (Π {K = K'} A') = do
 refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
 q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
 return (cong Π q)
meqNfTy (con c) (con c') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyCon c c')
  return (cong con p)
meqNfTy (μ {K = K} A B) (μ {K = K'} A' B') = do
  refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
  r    ← withE (λ ¬r → λ{refl → ¬r refl}) (meqNfTy B B')
  return (cong₂ μ q r)
meqNfTy (ne A) (ne A') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNeTy A A')
  return (cong ne p)
meqNfTy (Π _) (_ ⇒ _) = inj₁ λ()
meqNfTy (Π _) (ne _) = inj₁ λ()
meqNfTy (Π _) (con _) = inj₁ λ()
meqNfTy (Π _) (μ _ _) = inj₁ λ()
meqNfTy (_ ⇒ _) (Π _) = inj₁ λ()
meqNfTy (_ ⇒ _) (ne _) = inj₁ λ()
meqNfTy (_ ⇒ _) (con _) = inj₁ λ()
meqNfTy (_ ⇒ _) (μ _ _) = inj₁ λ()
meqNfTy (ƛ _) (ne _) = inj₁ λ()
meqNfTy (ne _) (Π _) = inj₁ λ()
meqNfTy (ne _) (_ ⇒ _) = inj₁ λ()
meqNfTy (ne _) (ƛ _) = inj₁ λ()
meqNfTy (ne _) (con _) = inj₁ λ()
meqNfTy (ne _) (μ _ _) = inj₁ λ()
meqNfTy (con _) (Π _) = inj₁ λ()
meqNfTy (con _) (_ ⇒ _) = inj₁ λ()
meqNfTy (con _) (ne _) = inj₁ λ()
meqNfTy (con _) (μ _ _) = inj₁ λ()
meqNfTy (μ _ _) (Π _) = inj₁ λ()
meqNfTy (μ _ _) (_ ⇒ _) = inj₁ λ()
meqNfTy (μ _ _) (ne _) = inj₁ λ()
meqNfTy (μ _ _) (con _) = inj₁ λ()

meqNeTy (` α) (` α') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyVar α α')
  return (cong ` p)
meqNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = do
  refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNeTy A A')
  r    ← withE (λ ¬r → λ{refl → ¬r refl}) (meqNfTy B B')
  return (cong₂ _·_ q r)
meqNeTy (` _) (_ · _) = inj₁ λ()
meqNeTy (_ · _) (` _) = inj₁ λ()

inv-complete : ∀{Φ K}{A A' : Φ ⊢⋆ K} → nf A ≡ nf A' → A' ≡β A
inv-complete {A = A}{A' = A'} p = trans≡β
  (soundness A')
  (trans≡β (≡2β (sym (cong embNf p))) (sym≡β (soundness A)))



inferTypeCon : ∀{Φ} → TermCon → Σ (T.TyCon _) λ c → A.TermCon {Φ} (con c) 
inferTypeCon (integer i)    = T.integer ,, A.integer i
inferTypeCon (bytestring b) = T.bytestring ,, A.bytestring b
inferTypeCon (string s)     = T.string ,, A.string s
inferTypeCon (bool b)       = T.bool ,, A.bool b
inferTypeCon unit           = T.unit ,, A.unit
inferTypeCon (pdata d)      = T.pdata ,, A.pdata d
inferTypeCon (bls12-381-g1-element e)      = T.bls12-381-g1-element ,, A.bls12-381-g1-element e
inferTypeCon (bls12-381-g2-element e)      = T.bls12-381-g2-element ,, A.bls12-381-g2-element e
inferTypeCon (bls12-381-mlresult r)   = T.bls12-381-mlresult ,, A.bls12-381-mlresult r

checkType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → (A : Φ ⊢Nf⋆ *)
  → Either TypeError (Γ ⊢ A)

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ)
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A)

checkType Γ L A = do
  A' ,, L ← inferType Γ L
  refl ← withE (typeMismatch _ _) (meqNfTy A A')
  return L
  
inferType Γ (` x) = do
  A ,, α ← inferVarType Γ x
  return (A ,, ` α)
inferType Γ (Λ K L) = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π A ,, Λ L)
inferType Γ (L ·⋆ A) = do
  K ,, B ,, L ← isPi (inferType Γ L)
  A ← checkKind _ A K
  return (B [ A ]Nf ,, L ·⋆ A / refl)
inferType Γ (ƛ A L) = do
  A ← isStar (inferKind _ A)
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ L)
inferType {Φ} Γ (L · M) = do
  A ,, B ,, L ← isFunType (inferType Γ L)
  M ← checkType Γ M A
  return (B ,, L · M)
inferType {Φ} Γ (con c) = do
  let tc ,, c = inferTypeCon {Φ} c
  return (con tc ,, con c)
inferType Γ (error A) = do
  A ← isStar (inferKind _ A)
  return (A ,, error A)
inferType Γ (builtin b) = inj₂ (btype b ,, builtin b / refl)
inferType Γ (wrap A B L) = do
  K ,, A ← isPat (inferKind _ A)
  B ← checkKind _ B K
  L ← checkType Γ L (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  return (μ A B ,, wrap A B L)
inferType Γ (unwrap L) = do
  K ,, A ,, B ,, L ← isMu (inferType Γ L)
  return (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B) ,, unwrap L refl)
```
 
