## Properties

Some properties about arrays

```
module Builtin.Array.Properties where

open import Builtin.Array.Base

open import Data.List
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _<?_; zero; suc; _<_; z≤n; s≤s; _≥_)
open import Data.Nat.Properties using (<-asym; <⇒≱)
open import Data.Integer using (ℤ; -[1+_]; +_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Fin using (fromℕ<; Fin; toℕ ; zero; suc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ)
open import Relation.Nullary using (Dec;yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Product using (∃; _,_)

absurd : ∀ {A : Set} → ⊥ → A
absurd ()
```

## Properties of `length`

```
private variable
  A : Set
  xs : Array A
  i : ℕ
```

## Properties of `length`

```
length-[] : length {A = A} [] ≡ 0
length-[] = refl

lengthOfArray-length : lengthOfArray (listToArray xs) ≡ + (length xs)
lengthOfArray-length = refl
```

## Properties of `indexArray`

Indexing outside the bounds of the array should fail.

```
indexArray-neg : indexArray xs (-[1+ i ]) ≡ nothing
indexArray-neg = refl

indexArray-≥ : i ≥ length xs → indexArray xs (+ i) ≡ nothing
indexArray-≥ {i = i} {xs = xs} i≥len
  with i <? length xs
... | yes i<len = absurd (<⇒≱ i<len i≥len)
... | no ¬le = refl
```

## Properties of `multiIndexArray`

### The `range` function

Ranges are needed for stating the `multiIndexArray-all` property below.

The list `range i n` constructs a list of length `n`, starting at `i` and
incrementing each subsequent element.

```
range : ℕ → ℕ → List ℕ
range n 0 = []
range n (suc len) = n ∷ range (suc n) len

_ : range 3 2 ≡ 3 ∷ 4 ∷ []
_ = refl

_ : range 123 0 ≡ []
_ = refl
```

The version that generates elements in `ℤ`, which is the type of indices in arrays.

```
rangeℤ : ℕ → ℕ → List ℤ
rangeℤ n len = map (+_) (range n len)
```

### Indexing all valid indices is the identity

Given an array `xs`, if we lookup all indices `0 .. length xs - 1`, we obtain a
list which is identical to xs (after converting back to an array). I.e. we prove the following lemma.

```text
multiIndexArray-all : multiIndexArray xs (rangeℤ 0 (length xs)) ≡ just (listToArray xs)
```

But first, we first we need to prove some lemmas.

`Drop` is used as an invariant for the `multiIndexArray-all` proof: `Drop i xs ys` states that dropping `i` elements from xs results in `ys`.

```
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
```

```
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Relation.Binary.PropositionalEquality.Properties
open ≡-Reasoning
open import Data.List.Properties using (drop-[])
```

Given `Drop i xs ys`, `i` is a valid index in `xs`, which we express using the `Fin` type.

```
Drop-index :
  ∀ {i} {y : A} {xs ys : List A}
  → Drop i xs (y ∷ ys)
  → ∃ λ (f : Fin (length xs)) → toℕ f ≡ i
Drop-index drop-zero = zero , refl
Drop-index (drop-suc drop)
  with Drop-index drop
... | f , refl = suc f , refl
```

Given `Drop i xs (y ∷ ys)`, looking `i` up in `xs` equals `y`.

```
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
```

If dropping `i` elements from `xs` results in a non-empty list `y ∷ ys`, it is
also possible to drop `suc i` elements, resulting in `ys`.

```
Drop-suc :
  ∀ {i} {xs : List A} {y ys}
  → Drop i xs (y ∷ ys)
  → Drop (suc i) xs ys
Drop-suc drop-zero = drop-suc drop-zero
Drop-suc (drop-suc drop) = drop-suc (Drop-suc drop)
```

### multiIndexArray all indices

The property is proven by generalizing over the start index of the range and the
resulting tail `ys` of `xs`, the invariant `Drop` captures the relation between
them.

```
multiIndexArray-all : multiIndexArray xs (rangeℤ 0 (length xs)) ≡ just (listToArray xs)
multiIndexArray-all {xs = xs} = go 0 xs xs drop-zero
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
