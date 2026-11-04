```
{-# OPTIONS --show-irrelevant #-}
module Builtin.Array.Base where

open import Data.Bool using (if_then_else_)
open import Data.List
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _<?_; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒<ᵇ)
open import Data.Integer using (ℤ; -[1+_]; +_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Fin using (fromℕ<; Fin; toℕ ; zero; suc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ)
open import Relation.Nullary using (Dec;yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Product using (∃; _,_)
```

## Semantics of arrays

The denotation of the array type is identical to that of lists, but we expect
that in practice arrays will be implemented in such a way that the
`lengthOfArray` and `indexArray` functions will be constant time and listToArray
may be nontrivial, requiring linear time.

```
Array : Set → Set
Array = List

private variable
  A : Set
```

## Built-in functions on Array

### Batch 6

```
lengthOfArray : Array A → ℤ
lengthOfArray xs = + (length xs)

listToArray : List A → Array A
listToArray xs = xs
```

### Batch 7

Indices are zero-based.

```
indexArray : Array A → ℤ → Maybe A
indexArray xs (-[1+ n ]) = nothing
indexArray xs (+ n)
  with n <? length xs
... | yes n<len = just (lookup xs (fromℕ< n<len))
... | no _ = nothing

multiIndexArray : Array A → List ℤ → Maybe (List A)
multiIndexArray _  [] = just []
multiIndexArray xs (i ∷ is)
  with indexArray xs i
... | nothing = nothing
... | just y
  with multiIndexArray xs is
... | nothing = nothing
... | just ys = just (y ∷ ys)
```

## Properties

```
private variable
  xs : Array A

length[] : length {A = A} [] ≡ 0
length[] = refl

indexArrayNeg : (n : ℕ) → indexArray xs (-[1+ n ]) ≡ nothing
indexArrayNeg _ = refl
```


```
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Relation.Binary.PropositionalEquality.Properties
open ≡-Reasoning
open import Data.List.Properties using (drop-[])

range : ℕ → ℕ → List ℕ
range n 0 = []
range n (suc len) = n ∷ range (suc n) len

_ : range 3 2 ≡ 3 ∷ 4 ∷ []
_ = refl

_ : range 123 0 ≡ []
_ = refl

rangeℤ : ℕ → ℕ → List ℤ
rangeℤ n len = map (+_) (range n len)

data Drop {A : Set} : ℕ → Array A → Array A → Set where

  drop-zero :
    ∀ {xs : Array A}
    -----------------
    → Drop 0 xs xs

  drop-suc :
    ∀ {n} {x : A} {xs} {ys : Array A}
    → Drop n xs ys
    -----------------------------
    → Drop (suc n) (x ∷ xs) ys

absurd : ∀ {A : Set} → ⊥ → A
absurd ()

Drop-index :
  ∀ {i} {y : A} {xs ys : List A}
  → Drop i xs (y ∷ ys)
  → ∃ λ (f : Fin (length xs)) → toℕ f ≡ i
Drop-index drop-zero = zero , refl
Drop-index (drop-suc drop)
  with Drop-index drop
... | f , refl = suc f , refl


Drop-indexArray :
  ∀ {i : ℕ} {x : A} {xs y ys}
  → Drop i (x ∷ xs) (y ∷ ys)
  → indexArray (x ∷ xs) (+ i) ≡ just y
Drop-indexArray {i = i} {x = x} {xs = xs} drop
  with Drop-index drop
... | f , refl
  with i <? length (x ∷ xs)
... | no ¬f<len = absurd (¬f<len (toℕ<n f))
... | yes f<len
  with fromℕ<-toℕ f f<len
... | H = cong just (Drop-lookup (fromℕ< f<len) (subst (λ x → Drop (toℕ x) _ _) (sym H) drop))

  where
    Drop-lookup :
      ∀ {xs y ys}
      → (n : Fin (length xs))
      → Drop (toℕ n) xs (y ∷ ys)
      → lookup xs n ≡ y
    Drop-lookup {xs = x ∷ xs} zero drop-zero = refl
    Drop-lookup {xs = x ∷ xs} (suc n) (drop-suc drop) = Drop-lookup n drop

Drop-suc :
  ∀ {i} {xs : List A} {y ys}
  → Drop i       xs (y ∷ ys)
  → Drop (suc i) xs ys
Drop-suc drop-zero = drop-suc drop-zero
Drop-suc (drop-suc drop) = drop-suc (Drop-suc drop)


multiIndexAll
  : (xs : Array A)
  → multiIndexArray xs (rangeℤ 0 (length xs)) ≡ just xs
multiIndexAll xs = go 0 xs xs drop-zero
  where
    go
      : (i : ℕ)
      → (xs : Array A)
      → (ys : Array A)
      → Drop i xs ys
      → multiIndexArray xs (rangeℤ i (length ys)) ≡ just ys
    go i [] ys drop-zero = refl
    go i (x ∷ xs) [] drop = refl
    go i (x ∷ xs) (y ∷ ys) drop
      rewrite Drop-indexArray drop
      rewrite go (suc i) (x ∷ xs) ys (Drop-suc drop) = refl
```
