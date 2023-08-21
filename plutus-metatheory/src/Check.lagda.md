---
layout: page
---
## Type checker

This module implements typechecking and inference for Scoped terms.

Scoped terms `ScopedTm` have scoped types `ScopedTy` which don't have kinds, so
kinds need to be inferred. Since we have two base kinds (`*` and `♯`) and the 
latter embeds into the former, there is some subtleties discussed below.
```
module Check where
```

## Imports

```
open import Data.Nat using (ℕ;zero;suc;_≟_;_<?_;_<_)
open import Data.Fin using (Fin;zero;suc;fromℕ<)
open import Data.List.Properties using (≡-dec)
open import Data.Vec as Vec using (Vec;[];_∷_)
open import Data.Vec.Properties using () renaming (≡-dec to ≡v-dec)
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong₂;cong;sym)
open import Relation.Nullary using (Dec;yes;no;_because_;¬_)
open import Agda.Builtin.String using (String)

import Utils as U
open import Utils.List using (List;[];_∷_)
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

open import Utils as U using (Kind;*;♯;_⇒_;Either;inj₁;inj₂;withE;Monad;dec2Either;_,_)
open Monad {{...}}

open import RawU using (TmCon;tmCon;TyTag)
open import Builtin.Signature using (_⊢♯) 
open import Builtin.Constant.Type

open import Type.Equality using (_≡β_;≡2β)
open _≡β_

open import Type.BetaNBE using (nf)
open import Type.BetaNBE.Soundness using (soundness)
open import Algorithmic using (_⊢_;Ctx;_∋_;sty2ty;ConstrArgs;[];_∷_;Cases;mkCaseType)
open import Algorithmic.Signature using (btype)
open _⊢_
open Ctx
open _∋_

open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf∅)

open import Builtin.Constant.AtomicType using (AtomicTyCon;decAtomicTyCon)
open AtomicTyCon
```

### Type Errors

We define the possible type errors that may occur.

```
data TypeError : Set where
  kindMismatch : (K K' : Kind) → ¬ (K ≡ K') → TypeError
  notFunKind  : (K : Kind) → (∀ K' J → ¬ (K ≡ K' ⇒ J)) → TypeError
  notPat  : (K : Kind) → (∀ K' → ¬ (K ≡ (K' ⇒ *) ⇒ (K' ⇒ *))) → TypeError
  UnknownType : TypeError
  notPi  : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ,⋆ K ⊢Nf⋆ *) → ¬ (A ≡ Π A')) →
    TypeError
  notMu : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ⊢Nf⋆ _)(B : Φ ⊢Nf⋆ K) → ¬ (A ≡ μ A' B))
    → TypeError
  notFunType : ∀{Φ}(A : Φ ⊢Nf⋆ *) → ((A' B : Φ ⊢Nf⋆ *) → ¬ (A ≡ A' ⇒ B)) → TypeError
  notSOP : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{n}(A' : Vec (List (Φ ⊢Nf⋆ *)) n) → ¬ (A ≡ SOP A')) → TypeError
  IndexOutOfBounds : ∀{i n} → ¬(i < n) → TypeError
  TooManyConstrArgs : TypeError
  TooFewConstrArgs : TypeError
  TooFewCases : TypeError
  TooManyCases : TypeError
  typeMismatch : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → ¬ (A ≡ A') → TypeError
  builtinError : TypeError
  Unimplemented : String → TypeError
```

### Auxiliary Functions

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ (i : Fin (len⋆ Φ)) → Σ Kind (Φ ∋⋆_)
inferTyVar (Φ ,⋆ K) zero    = K ,, Z
inferTyVar (Φ ,⋆ K) (suc i) = let J ,, α = inferTyVar Φ i in  J ,, S α

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

isFunKind : ∀{Φ}
       → Σ Kind (Φ ⊢Nf⋆_)
       → Either TypeError (Σ Kind λ K → Σ Kind λ J → Φ ⊢Nf⋆ K ⇒ J)
isFunKind (K ⇒ J ,, A) = return (K ,, J ,, A)
isFunKind (♯ ,, _)     = inj₁ (notFunKind ♯ λ _ _ ())
isFunKind (* ,, _)     = inj₁ (notFunKind * λ _ _ ())
  
isPat : ∀{Φ}
       → Σ Kind (Φ ⊢Nf⋆_)
       → Either TypeError (Σ Kind λ K → Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *))
isPat (* ,, A) = inj₁ (notPat * λ _ ())
isPat (♯ ,, A) = inj₁ (notPat ♯ λ _ ())
isPat ((* ⇒ K₁) ,, A) = inj₁ (notPat (* ⇒ K₁) λ _ ())
isPat ((♯ ⇒ K₁) ,, A) = inj₁ (notPat (♯ ⇒ K₁) λ _ ())
isPat (((K ⇒ K₂) ⇒ *) ,, A) = inj₁ (notPat ((K ⇒ K₂) ⇒ *) λ _ ())
isPat (((K ⇒ K₂) ⇒ ♯) ,, A) = inj₁ (notPat ((K ⇒ K₂) ⇒ ♯) λ _ ())
isPat (((K ⇒ *) ⇒ (K₁ ⇒ *)) ,, A) = do
      refl ← withE (kindMismatch _ _) (dec2Either (decKind K K₁))
      return (K ,, A) 
isPat (((K ⇒ *) ⇒ (K₁ ⇒ ♯)) ,, A) = inj₁ (notPat ((K ⇒ *) ⇒ (K₁ ⇒ ♯)) λ _ ())
isPat (((K ⇒ *) ⇒ (K₁ ⇒ (K₃ ⇒ K₄))) ,, A) = inj₁ (notPat ((K ⇒ *) ⇒ (K₁ ⇒ (K₃ ⇒ K₄))) λ _ ())
isPat (((K ⇒ ♯) ⇒ (K₁ ⇒ K₃)) ,, A) = inj₁ (notPat ((K ⇒ ♯) ⇒ (K₁ ⇒ K₃)) λ _ ())
isPat (((K ⇒ (K₂ ⇒ K₄)) ⇒ (K₁ ⇒ K₃)) ,, A) = inj₁ (notPat ((K ⇒ (K₂ ⇒ K₄)) ⇒ (K₁ ⇒ K₃)) λ _ ())

isPi :  ∀{Φ Γ}
       → Σ (Φ ⊢Nf⋆ *) (Γ ⊢_)
       → Either TypeError (Σ Kind λ K → Σ (Φ ,⋆ K ⊢Nf⋆ *) λ A → Γ ⊢ Π A)
isPi (Π A ,, L)       = return (_ ,, A ,, L)
isPi (A ⇒ B ,, _)     = inj₁ (notPi (A ⇒ B) (λ _ ()))
isPi (ne A  ,, _)     = inj₁ (notPi (ne A) (λ _ ()))
isPi (con {Φ} c ,, _) = inj₁ (notPi (con {Φ} c) (λ _ ()))
isPi (μ A B ,, _)     = inj₁ (notPi (μ A B) (λ _ ()))
isPi (SOP x ,, _)     = inj₁ (notPi (SOP x) (λ _ ()))

isFunType :  ∀{Φ Γ}
       → Σ (Φ ⊢Nf⋆ *) (Γ ⊢_)
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Σ (Φ ⊢Nf⋆ *) λ B → Γ ⊢ A ⇒ B)
isFunType (A ⇒ B ,, L ) =  return (A ,, B ,, L)
isFunType (Π A ,, _) = inj₁ (notFunType (Π A) (λ _ _ ()))
isFunType (ne A  ,, _ ) = inj₁ (notFunType (ne A) (λ _ _ ()))
isFunType (con {Φ} c ,, _) = inj₁ (notFunType (con {Φ} c) (λ _ _ ()))
isFunType (μ A B ,, _) = inj₁ (notFunType (μ A B) (λ _ _ ()))
isFunType (SOP x ,, _) = inj₁ (notFunType (SOP x) (λ _ _ ()))
  
isMu :  ∀{Φ Γ}
       → Σ (Φ ⊢Nf⋆ *) (Γ ⊢_)
       → Either TypeError (Σ Kind λ K → Σ (Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *)) λ A → Σ (Φ ⊢Nf⋆ K) λ B → Γ ⊢ μ A B)
isMu (μ A B ,, L) = return (_ ,, A ,, B ,, L)
isMu (Π A ,, _) = inj₁ (notMu (Π A) (λ _ _ ()))
isMu (ne A  ,, _) = inj₁ (notMu (ne A) (λ _ _ ()))
isMu (con {Φ} c ,, _) = inj₁ (notMu (con {Φ} c) (λ _ _ ()))
isMu (A ⇒ B ,, _) = inj₁ (notMu (A ⇒ B) (λ _ _ ()))
isMu (SOP x ,, _) = inj₁ (notMu (SOP x) (λ _ _ ()))

isSOPType :  ∀{Φ}
       → (Φ ⊢Nf⋆ *) 
       → Either TypeError (Σ ℕ (λ n → Vec (List (Φ ⊢Nf⋆ *)) n ))
isSOPType (Π A) = inj₁ (notSOP (Π A) (λ _ ()))
isSOPType (A ⇒ B) = inj₁ (notSOP (A ⇒ B) (λ _ ()))
isSOPType (ne A) = inj₁ (notSOP (ne A) (λ _ ()))
isSOPType (con c) = inj₁ (notSOP (con c) (λ _ ()))
isSOPType (μ A B) = inj₁ (notSOP (μ A B) (λ _ ()))
isSOPType (SOP {n = n} TSS) = return (n ,, TSS)

isSOP  : ∀{Φ Γ}
       → Σ (Φ ⊢Nf⋆ *) (Γ ⊢_)
       → Either TypeError (Σ ℕ λ n → Σ (Vec (List (Φ ⊢Nf⋆ *)) n) λ TSS → Γ ⊢ SOP TSS) 
isSOP (Π A ,, _) = inj₁ (notSOP (Π A) (λ _ ()))
isSOP ((A ⇒ B) ,, _) = inj₁ (notSOP (A ⇒ B) (λ _ ()))
isSOP (ne A ,, _) = inj₁ (notSOP (ne A) (λ _ ()))
isSOP (con c ,, _) = inj₁ (notSOP (con c) (λ _ ()))
isSOP (μ A B ,, x) = inj₁ (notSOP (μ A B) (λ _ ()))
isSOP (SOP {n = n} TSS ,, x) = return (n ,, (TSS ,, x))

chkIdx : ∀ (i n : ℕ) → Either TypeError (Fin n)
chkIdx i n with i <? n 
... | no ¬p = inj₁ (IndexOutOfBounds ¬p)
... | yes p = return (fromℕ< p)
```
We have two base kinds, * and ♯, and we have an embedding of ♯ into *

   con : Φ ⊢⋆ ♯
         ------
       → Φ ⊢⋆ *

Hence, when inferring a kind we sometimes need to decide if we want a ♯ kind or a * kind. For example,

  con (atomic aInteger) : ScopedTy 0 

  might be inferred as kind ♯

  1.    ne (^ (atomic aInteger))
  
  or as kind *
  
  2.    con (ne (^ (atomic aInteger)))

Whenever we have a constant of kind `♯` we embed it into `*` using `con`.
This means that a composition of, for instance a list (kind `♯ ⇒ ♯`) applied 
to a constant (which will be of kind `*`) doesn't match exactly. So we relax 
this condition  when checking kinds and allow
  1. Checking a `*`-kinded type against `♯`, whenever the type is of the form `con A` : 
       we "downgrade" the type to A of kind `♯`. 
  2. Checking a `♯`-kinded type against `*`: 
       we "upgrade" the type to `*` using `con`.

Another option to one may try is to leave alone kind `♯` and only upgrade it as
needed. However, this is not easy, as when one detects the need to upgrade a ♯ 
to *, it might be too late. One example of this, would be in the case of `μ`, 
where one needs a kind (K ⇒ *) ⇒ (K ⇒ *). Here, it is difficult to upgrade a 
kind (K ⇒ ♯) ⇒ (K ⇒ ♯) because one would need to find the places inside the type
to insert the appropriate `con`s.
 
```
inferTyCon : ∀ {Φ} {K} → TyCon K → Σ Kind (Φ ⊢Nf⋆_)
inferTyCon {K = K} tycon = K ,, (ne (^ tycon))

checkKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → ∀ K → Either TypeError (Φ ⊢Nf⋆ K)
inferKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))

inferKind-List : ∀ Φ (xs : U.List (ScopedTy (len⋆ Φ))) → Either TypeError (List (Φ ⊢Nf⋆ *))
inferKind-List Φ U.[] = return []
inferKind-List Φ (x U.∷ xs) = do 
            A  ← checkKind Φ x * 
            AS ← inferKind-List Φ xs 
            return (A ∷ AS)

inferKind-VecList : ∀ Φ (xss : U.List (U.List (ScopedTy (len⋆ Φ)))) → Either TypeError (Vec (List (Φ ⊢Nf⋆ *)) (U.length xss))
inferKind-VecList Φ U.[] = return []
inferKind-VecList Φ (xs U.∷ xss) = do 
              AS ← inferKind-List Φ xs 
              ASS ← (inferKind-VecList Φ xss)
              return (AS ∷ ASS)

checkKind-aux : ∀{Φ} → (Σ Kind (Φ ⊢Nf⋆_)) → ∀ K → Either TypeError (Φ ⊢Nf⋆ K)
checkKind-aux (* ,, A)        * = return A
checkKind-aux (♯ ,, A)        * = return (con A) --upgrade from ♯ to *
checkKind-aux ((K ⇒ J) ,, _)  * = inj₁ (kindMismatch (K ⇒ J) * (λ ()))
checkKind-aux (* ,, con A)    ♯ = return A       --downgrade from * to ♯
checkKind-aux (* ,, _)        ♯ = inj₁ (kindMismatch ♯ * (λ ()))
checkKind-aux (♯ ,, A)        ♯ = return A
checkKind-aux ((K ⇒ J) ,, _)  ♯ = inj₁ (kindMismatch (K ⇒ J) ♯ (λ ()))
checkKind-aux (* ,, A) (J ⇒ J₁) = inj₁ (kindMismatch * (J ⇒ J₁) (λ ()))
checkKind-aux (♯ ,, A) (J ⇒ J₁) = inj₁ (kindMismatch ♯ (J ⇒ J₁) (λ ()))
checkKind-aux (K ,, A) K'@(_ ⇒ _) = do 
            refl ← withE (kindMismatch _ _) (dec2Either (decKind K K'))
            return A

checkKind Φ A K = do 
             KA ← inferKind Φ A
             checkKind-aux KA K 



-- When the kind is ♯ we may convert it to a constant of kind *
addCon : ∀ {Φ} →  (Σ Kind (Φ ⊢Nf⋆_)) → (Σ Kind (Φ ⊢Nf⋆_))
addCon (♯ ,, snd) = * ,, con snd
addCon kA = kA

-- But we don't need to add con to variables, because ♯ only should occur under `pair` or `list`
inferKind Φ (` α) = let K ,, β = inferTyVar Φ α in return (K ,, ne (` β))
inferKind Φ (A ⇒ B) = do
          A ← checkKind Φ A *
          B ← checkKind Φ B * 
          return (* ,, A ⇒ B)
inferKind Φ (Π K A) = do
          A ← checkKind (Φ ,⋆ K) A *
          return (* ,, Π A)
inferKind Φ (ƛ K A) = do
  J ,, A ← inferKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ A)
inferKind Φ (A · B) =  do
          KA ← inferKind Φ A
          (K ,, J ,, A) ← isFunKind KA
          B ← checkKind Φ B K
          return (addCon (J ,, nf (embNf A · embNf B)))
inferKind Φ (con tc) = return (addCon (inferTyCon tc))
inferKind Φ (μ A B) = do
          KA ← inferKind Φ A
          K ,, A ← isPat KA
          B ← checkKind Φ B K
          return (* ,, μ A B)
inferKind Φ (SOP x) = do 
              xss ← inferKind-VecList Φ x  
              return (* ,, SOP xss)
```

Some examples to check that everything is working as expected

```
private module _ where 

  int : ∀{n} → ScopedTy n
  int = con (atomic aInteger)
   
  -- integer
  _ :  inferKind ∅ int ≡ inj₂ (* ,, con (ne (^ (atomic aInteger))))
  _ = refl

  -- list of integers
  _ : inferKind ∅ (con list · int) ≡ inj₂ (* ,, con (ne (^ list · ne (^ (atomic aInteger))))) 
  _ = refl

  -- list of lists of integers
  _ : inferKind ∅ (con list · (con list · int)) ≡ inj₂ (* ,, con (ne (^ list · ne (^ list · ne (^ (atomic aInteger))))))
  _ = refl

  _ : inferKind ∅ (con list · int) ≡ inj₂ (* ,, con (ne (^ list · ne (^ (atomic aInteger)))))
  _ = refl

  -- pair of some variables of kind ♯
  _ : inferKind (∅ ,⋆ ♯ ,⋆ ♯) (con pair · ` zero · ` (suc zero)) ≡ inj₂ (* ,, (con (ne (^ pair · ne (` Z) · ne (` (S Z))))))
  _ = refl

  -- we can't have kind * under a pair
  _ : inferKind (∅ ,⋆ ♯ ,⋆ *) (con pair · ` zero · ` (suc zero)) ≡ inj₁ (kindMismatch ♯ * (λ ()))
  _ = refl

  -- list of integer under a function
  _ : inferKind ∅ ((con list · int) ⇒ int) ≡ inj₂ (* ,, (con (nf (^ list · ^ (atomic aInteger))) ⇒ con (ne (^ (atomic aInteger)))))
  _ = refl

  -- Some Π type. Note that the variable is of kind ♯ 
  _ : inferKind ∅ (Π ♯ (con list · ` zero)) ≡ inj₂ (* ,, Π (con (ne (^ list · ne (` Z)))))
  _ = refl

  -- The variable to which we apply the list cannot be *
  _ : inferKind ∅ (Π * (con list · ` zero)) ≡ inj₁ (kindMismatch ♯ * (λ ()))
  _ = refl

  -- Some mu type, where we need to upgrade ♯.
  _ : inferKind ∅ (μ (ƛ (* ⇒ *) (ƛ * int)) int) ≡ inj₂ (* ,, μ (ƛ (ƛ (con (ne (^ (atomic aInteger)))))) (con (ne (^ (atomic aInteger)))))
  _ = refl
```

### Inferring the type of variables

```
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
```

### Some Decidability predicates

```
decTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → Dec (α ≡ α')
decTyVar Z     Z      = yes refl 
decTyVar (S α) (S α') with (decTyVar α α')
...        | yes refl = yes refl 
...        | no  ¬p   = (no (λ { refl → ¬p refl}))
decTyVar Z     (S α') = (no λ())
decTyVar (S α) Z      = (no λ())

decNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → Dec (A ≡ A')
decNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → Dec (A ≡ A')

decNfTy-List : ∀{Φ K}(xs ys : List (Φ ⊢Nf⋆ K)) → Dec (xs ≡ ys)
decNfTy-List [] [] = yes refl
decNfTy-List [] (x ∷ ys) = no λ()
decNfTy-List (x ∷ xs) [] = no λ()
decNfTy-List (x ∷ xs) (y ∷ ys) = dcong₂ _∷_ (λ { refl → refl ,, refl}) (decNfTy x y) (decNfTy-List xs ys)

decNfTy-VecList : ∀{Φ n K}(xss yss : Vec (List (Φ ⊢Nf⋆ K)) n) → Dec (xss ≡ yss)
decNfTy-VecList [] [] = yes refl
decNfTy-VecList (xs ∷ xss) (ys ∷ yss) = dcong₂ _∷_ (λ { refl → refl ,, refl}) (decNfTy-List xs ys) (decNfTy-VecList xss yss)

decTyCon : ∀{Φ}(c c' : TyCon Φ) → Dec (c ≡ c')
decTyCon (atomic x) (atomic y) = dcong atomic (λ {refl → refl}) (decAtomicTyCon x y)
decTyCon list list = yes refl
decTyCon pair pair = yes refl

decNfTy (Π {K = K} A) (Π {K = K'} A') = dhcong (λ k t → Π {K = k} t) 
                                                (λ {refl → refl ,, refl}) 
                                                (decKind K K')
                                                (decNfTy A) 
decNfTy (Π _) (_ ⇒ _)     = no λ()
decNfTy (Π _) (ne _)      = no λ()
decNfTy (Π _) (con _)     = no λ()
decNfTy (Π _) (μ _ _)     = no λ()
decNfTy (_ ⇒ _) (Π _)     = no λ()
decNfTy (A ⇒ B) (A' ⇒ B') = dcong₂ _⇒_ (λ {refl → refl ,, refl }) (decNfTy A A') (decNfTy B B') 
decNfTy (_ ⇒ _) (ne _)    = no λ()
decNfTy (_ ⇒ _) (con _)   = no λ()
decNfTy (_ ⇒ _) (μ _ _)   = no λ()
decNfTy (ƛ A) (ƛ A')      = dcong ƛ (λ {refl → refl}) (decNfTy A A')
decNfTy (ƛ _) (ne _)      = no λ()
decNfTy (ne _) (Π _)      = no λ()
decNfTy (ne _) (_ ⇒ _)    = no λ()
decNfTy (ne _) (ƛ _)      = no λ()
decNfTy (ne A) (ne A')    = dcong ne (λ {refl → refl}) (decNeTy A A')
decNfTy (ne _) (con _)    = no λ()
decNfTy (ne _) (μ _ _)    = no λ()
decNfTy (con _) (Π _)     = no λ()
decNfTy (con _) (_ ⇒ _)   = no λ()
decNfTy (con _) (ne _)    = no λ()
decNfTy (con t) (con u)   = dcong con (λ {refl → refl}) (decNfTy t u)
decNfTy (con _) (μ _ _)   = no λ()
decNfTy (μ _ _) (Π _)     = no λ()
decNfTy (μ _ _) (u ⇒ u₁)  = no λ()
decNfTy (μ _ _) (ne _)    = no λ()
decNfTy (μ _ _) (con _)   = no λ()
decNfTy (μ {K = K} A B) (μ {K = K'} A' B') = dhcong₂ (λ k x y → μ {K = k} x y)
                                                     (λ { refl → refl ,, refl ,, refl }) 
                                                     (decKind K K') 
                                                     (decNfTy A)
                                                     (decNfTy B)
decNfTy (SOP x) (Π A')     = no λ()
decNfTy (SOP x) (A' ⇒ A'') = no λ()
decNfTy (SOP x) (ne x₁)    = no λ()
decNfTy (SOP x) (con A')   = no λ()
decNfTy (SOP x) (μ A' A'') = no λ()
decNfTy (Π A) (SOP x)      = no λ()
decNfTy (A ⇒ A₁) (SOP x)   = no λ()
decNfTy (ne x₁) (SOP x)    = no λ()
decNfTy (con A) (SOP x)    = no λ()
decNfTy (μ A A₁) (SOP x)   = no λ()
decNfTy (SOP {n = n} x) (SOP {n = m} y) with n ≟ m
... | no ¬p    = no (λ {refl → ¬p refl})
... | yes refl with decNfTy-VecList x y                                         
...            | no ¬p = no (λ {refl  → ¬p refl})
...            | yes refl = yes refl

decNeTy (` α) (` α') = dcong ` (λ {refl → refl}) (decTyVar α α')
decNeTy (` _) (_ · _) = no λ()
decNeTy (` _) (^ _)   = no λ()
decNeTy (_ · _) (` _) = no λ()
decNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = dhcong₂ (λ k t u → _·_ {K = k} t u)
                                                         (λ { refl → refl ,, refl ,, refl }) 
                                                         (decKind K K') 
                                                         (decNeTy A) 
                                                         (decNfTy B)
decNeTy (_ · _) (^ _) = no λ()
decNeTy (^ _) (` _)   = no λ()
decNeTy (^ _) (_ · _) = no λ()
decNeTy (^ C) (^ C')  = dcong ^ (λ {refl → refl}) (decTyCon C C')
```

## The main functions for checking and inferring types

```
checkType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → (A : Φ ⊢Nf⋆ *)
  → Either TypeError (Γ ⊢ A)

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ)
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A)

checkType Γ L A = do
  A' ,, L ← inferType Γ L
  let d = decNfTy A A'
  refl ← withE (typeMismatch _ _) (dec2Either d)
  return L
  
checkConstrArgs-List : ∀{Φ}(Γ : Ctx Φ) 
               → U.List (ScopedTm (len Γ)) 
               → (AS : List (Φ ⊢Nf⋆ *))
               → Either TypeError (ConstrArgs Γ AS)
checkConstrArgs-List Γ U.[] [] = return []
checkConstrArgs-List Γ U.[] (A ∷ AS) = inj₁ TooFewConstrArgs
checkConstrArgs-List Γ (c U.∷ cs) [] = inj₁ TooManyConstrArgs
checkConstrArgs-List Γ (c U.∷ cs) (A ∷ AS) = do 
         t ← checkType Γ c A 
         ts ← checkConstrArgs-List Γ cs AS
         return (t ∷ ts)

checkCases-List : ∀{Φ}(Γ : Ctx Φ) 
               → (B : Φ ⊢Nf⋆ *)
               → U.List (ScopedTm (len Γ)) 
               → ∀{n}(TSS : Vec (List (Φ ⊢Nf⋆ *)) n)
               → Either TypeError (Cases Γ B TSS)
checkCases-List Γ B U.[] [] = return []
checkCases-List Γ B U.[] (TS ∷ TSS) = inj₁ TooFewCases
checkCases-List Γ B (c U.∷ cs) [] = inj₁ TooManyCases
checkCases-List Γ B (c U.∷ cs) (TS ∷ TSS) = do 
           x ← checkType Γ c (mkCaseType B TS)
           xs ← checkCases-List Γ B cs TSS
           return (x ∷ xs)               

inferType Γ (` x) = do
  A ,, α ← inferVarType Γ x
  return (A ,, ` α)
inferType Γ (Λ K L) = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π A ,, Λ L)
inferType Γ (L ·⋆ A) = do
  t ← inferType Γ L
  K ,, B ,, L ← isPi t
  A ← checkKind _ A K
  return (B [ A ]Nf ,, L ·⋆ A / refl)
inferType Γ (ƛ A L) = do
  A ← checkKind _ A *
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ L)
inferType {Φ} Γ (L · M) = do
  ty ← inferType Γ L
  A ,, B ,, L ← isFunType ty
  M ← checkType Γ M A
  return (B ,, L · M)
inferType Γ (con (tmCon t x)) = do 
  return (con (subNf∅ (sty2ty t)) ,, con x refl)
inferType Γ (error A) = do
  A ← checkKind _ A *
  return (A ,, error A)
inferType Γ (builtin b) = do 
  let bty = btype b
  return (bty ,, builtin b / refl)
inferType Γ (wrap A B L) = do
  KA ← inferKind _ A
  K ,, A ← isPat KA
  B ← checkKind _ B K
  L ← checkType Γ L (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  return (μ A B ,, wrap A B L)
inferType Γ (unwrap L) = do
  TL ← inferType Γ L
  K ,, A ,, B ,, L ← isMu TL
  return (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B) ,, unwrap L refl)
inferType Γ (constr A i cs) = do
         -- A is of kind * with type SOP TSS
         B ← checkKind _ A *
         (n ,, TSS) ← isSOPType B
         -- i < length cs
         e ← chkIdx i n
         -- cs has type Vec.lookup TSS e           
         L ← checkConstrArgs-List Γ cs (Vec.lookup TSS e)
         return ((SOP TSS) ,, (constr e TSS refl L)) 
inferType Γ (case A x cs) = do 
             B ← checkKind _ A *
             -- check x is of SOP type
             L ← inferType Γ x
             (n ,, TSS ,, t) ← isSOP L
             cases ← checkCases-List Γ B cs TSS
             return (B ,, case t cases)
```
