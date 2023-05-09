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
open import Data.List using (map;[];_∷_)
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong₂;cong;sym)
open import Relation.Nullary using (Dec;yes;no;_because_;¬_)
open import Agda.Builtin.String using (String)

import Utils as U
open import Utils.Decidable using (dcong;dcong₂;dhcong;dhcong₂)
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

open import Utils using (Kind;*;♯;_⇒_;Either;inj₁;inj₂;withE;Monad;dec2Either;_,_)
open Monad {{...}}

open import RawU using (TmCon;tmCon;TyTag)
open import Builtin.Signature using (_⊢♯) 
open import Builtin.Constant.Type

open import Type.Equality using (_≡β_;≡2β)
open _≡β_

open import Type.BetaNBE using (nf)
open import Type.BetaNBE.Soundness using (soundness)
open import Algorithmic using (_⊢_;Ctx;_∋_;sty2ty)
open import Algorithmic.Signature using (btype)
open _⊢_
open Ctx
open _∋_

open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf∅)

open import Builtin.Constant.AtomicType using (AtomicTyCon;decAtomicTyCon)
open AtomicTyCon
--import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) as T
--import Builtin.Constant.Type ℕ ScopedTy as S
import Builtin.Constant.Type as T
import Builtin.Constant.Type as S

--import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as A
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
  Unimplemented : String → TypeError

decKind : (K K' : Kind) → Dec (K ≡ K')
decKind * * = yes refl
decKind ♯ ♯ = yes refl
decKind * ♯ = no λ()
decKind ♯ * = no λ()
decKind * (K' ⇒ J') = no λ() 
decKind ♯ (K' ⇒ J') = no λ() 
decKind (K ⇒ J) * = no λ()
decKind (K ⇒ J) ♯ = no λ()
decKind (K ⇒ J) (K' ⇒ J') = dcong₂ _⇒_ (λ { refl → refl ,, refl}) (decKind K K') (decKind J J')

isStar : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Φ ⊢Nf⋆ *)
isStar p = do
  * ,, A ← p
   where (K ⇒ J ,, _) → inj₁ (notStar (K ⇒ J) λ())
         (♯ ,, _) → inj₁ (notStar ♯ λ())
  return A

isFunKind : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Σ Kind λ J → Φ ⊢Nf⋆ K ⇒ J)
isFunKind p = do
  K ⇒ J ,, A ← p
    where (♯ ,, _) → inj₁ (notFunKind ♯ λ _ _ ())
          (* ,, _) → inj₁ (notFunKind * λ _ _ ())
  return (K ,, J ,, A)

isPat : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *))
isPat p =
 do
  (K ⇒ *) ⇒ (K' ⇒ *) ,, A ← p
    where
      (* ,, _) → inj₁ (notPat * λ _ ())
      (♯ ,, _) → inj₁ (notPat ♯ λ _ ())
      (K@(_ ⇒ *) ,, _) → inj₁ (notPat K λ _ ())
      (K@(_ ⇒ ♯) ,, _) → inj₁ (notPat K λ _ ())
      (K@(_ ⇒ (_ ⇒ (_ ⇒ _))) ,, _) → inj₁ (notPat K λ _ ())
      (K@(* ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@(* ⇒ (_ ⇒ ♯)) ,, _) → inj₁ (notPat K λ _ ())
      (K@(♯ ⇒ (_ ⇒ ♯)) ,, _) → inj₁ (notPat K λ _ ())
      (K@(♯ ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ ♯) ⇒ (_ ⇒ ♯)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ *) ⇒ (_ ⇒ ♯)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ ♯) ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ (_ ⇒ _)) ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ (_ ⇒ _)) ⇒ (_ ⇒ ♯)) ,, _) → inj₁ (notPat K λ _ ())
  refl ← withE (kindMismatch _ _) (dec2Either (decKind K K'))
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
--inferKindCon : ∀ Φ (c : S.TyCon (len⋆ Φ)) → Either TypeError (T.TyCon Φ)

{-
inferKindCon Φ (S.list A) = do
  A ← isStar (inferKind Φ A)
  return (T.list A)
inferKindCon Φ (S.pair A B) = do
  A ← isStar (inferKind Φ A)
  B ← isStar (inferKind Φ B)  
  return (T.pair A B)
inferKindCon Φ (S.atomic A)= inj₂ (T.atomic A)
-}

checkKind Φ A K = do
  K' ,, A ← inferKind Φ A
  refl ← withE (kindMismatch _ _) (dec2Either (decKind K K'))
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
inferKind Φ (con {K} tc) =
  return (K ,, ne (^ tc))
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

decTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → Dec (α ≡ α')
decTyVar Z     Z      = yes refl 
decTyVar (S α) (S α') with (decTyVar α α')
... | yes refl = yes refl 
... | no  ¬p   = no (λ { refl → ¬p refl})
decTyVar Z     (S α') = no λ()
decTyVar (S α) Z      = no λ()

decNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → Dec (A ≡ A')
decNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → Dec (A ≡ A')
decTyCon : ∀{Φ}(c c' : T.TyCon Φ) → Dec (c ≡ c')
decTyCon (atomic x) (atomic y) = dcong T.atomic (λ {refl → refl}) (decAtomicTyCon x y)
decTyCon list list = yes refl
decTyCon pair pair = yes refl

decNfTy (Π {K = K} A) (Π {K = K'} A') = dhcong (λ k t → Π {K = k} t) 
                                                (λ {refl → refl ,, refl}) 
                                                (decKind K K')
                                                (decNfTy A) 
decNfTy (Π t) (u ⇒ u₁) = no λ()
decNfTy (Π t) (ne x) = no λ()
decNfTy (Π t) (con u) = no λ()
decNfTy (Π t) (μ u u₁) = no λ()
decNfTy (t ⇒ t₁) (Π u) = no λ()
decNfTy (A ⇒ B) (A' ⇒ B') = dcong₂ _⇒_ (λ {refl → refl ,, refl }) (decNfTy A A') (decNfTy B B') 
decNfTy (t ⇒ t₁) (ne x) = no λ()
decNfTy (t ⇒ t₁) (con u) = no λ()
decNfTy (t ⇒ t₁) (μ u u₁) = no λ()
decNfTy (ƛ A) (ƛ A') = dcong ƛ (λ {refl → refl}) (decNfTy A A')
decNfTy (ƛ t) (ne x) = no λ()
decNfTy (ne x) (Π u) = no λ()
decNfTy (ne x) (u ⇒ u₁) = no λ()
decNfTy (ne x) (ƛ u) = no λ()
decNfTy (ne A) (ne A') = dcong ne (λ {refl → refl}) (decNeTy A A')
decNfTy (ne x) (con u) = no λ()
decNfTy (ne x) (μ u u₁) = no λ()
decNfTy (con t) (Π u) =  no λ()
decNfTy (con t) (u ⇒ u₁) =  no λ()
decNfTy (con t) (ne x) =  no λ()
decNfTy (con t) (con u) = dcong con (λ {refl → refl}) (decNfTy t u)
decNfTy (con t) (μ u u₁) =  no λ()
decNfTy (μ t t₁) (Π u) =  no λ()
decNfTy (μ t t₁) (u ⇒ u₁) =  no λ()
decNfTy (μ t t₁) (ne x) =  no λ()
decNfTy (μ t t₁) (con u) =  no λ()
decNfTy (μ {K = K} A B) (μ {K = K'} A' B') = dhcong₂ (λ k x y → μ {K = k} x y)
                                                     (λ { refl → refl ,, refl ,, refl }) 
                                                     (decKind K K') 
                                                     (decNfTy A)
                                                     (decNfTy B)

decNeTy (` α) (` α') = dcong ` (λ {refl → refl}) (decTyVar α α')
decNeTy (` _) (_ · _) = no λ()
decNeTy (` _) (^ _) = no λ()
decNeTy (_ · _) (` _) = no λ()
decNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = dhcong₂ (λ k t u → _·_ {K = k} t u)
                                                         (λ { refl → refl ,, refl ,, refl }) 
                                                         (decKind K K') 
                                                         (decNeTy A) 
                                                         (decNfTy B)
decNeTy (_ · _) (^ _) = no λ()
decNeTy (^ _) (` _) = no λ()
decNeTy (^ _) (_ · _) = no λ()
decNeTy (^ C) (^ C') = dcong ^ ((λ {refl → refl})) (decTyCon C C')

inv-complete : ∀{Φ K}{A A' : Φ ⊢⋆ K} → nf A ≡ nf A' → A' ≡β A
inv-complete {A = A}{A' = A'} p = trans≡β
  (soundness A')
  (trans≡β (≡2β (sym (cong embNf p))) (sym≡β (soundness A)))

checkType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → (A : Φ ⊢Nf⋆ *)
  → Either TypeError (Γ ⊢ A)

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ)
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A)

checkType Γ L A = do
  A' ,, L ← inferType Γ L
  refl ← withE (typeMismatch _ _) (dec2Either (decNfTy A A'))
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
inferType {Φ} Γ (con (tmCon t x)) = return ((con (subNf∅ (sty2ty t))) ,, con x refl)
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
