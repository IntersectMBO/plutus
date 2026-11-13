---
title: Builtin.ByteString.Base
layout: page
---

```
module Builtin.ByteString.Base where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _/_; _%_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-comm; <ᵇ⇒<)
open import Data.Nat.DivMod using (m<n*o⇒m/o<n; m%n<n; m≡m%n+[m/n]*n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Function.Base using (_∘_; _$_)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
import Data.Fin as Fin
import Data.Fin.Properties as Fin
import Data.Vec as Vec
import Data.Nat as ℕ
import Builtin.ByteString.Byte as Byte

open import Builtin.ByteString.Byte using (Byte; byteToNat; natToByte)
```

## ByteString

```

infixr 5 _∷_

data ByteString : Set where
  []  : ByteString
  _∷_ : Byte → ByteString → ByteString
```

### Decidable Equality

```
_≟_ : (bs₁ bs₂ : ByteString) → Dec (bs₁ ≡ bs₂)
[] ≟ [] = yes refl
[] ≟ (_ ∷ _) = no λ()
(_ ∷ _) ≟ [] = no λ()
(x ∷ xs) ≟ (y ∷ ys) with x Byte.≟ y
... | yes refl = Dec.map′ (cong (x ∷_)) (λ { refl → refl }) (xs ≟ ys)
... | no x≢y   = no λ { refl → x≢y refl }
```

### Operations on ByteStrings

```
_++_ : ByteString → ByteString → ByteString
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ByteString → ℕ
length []       = 0
length (_ ∷ xs) = 1 + length xs

take : ℕ → ByteString → ByteString
take zero    _        = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → ByteString → ByteString
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (_ ∷ xs) = drop n xs

index : ℕ → ByteString → Maybe Byte
index _       []       = nothing
index zero    (x ∷ _)  = just x
index (suc i) (_ ∷ xs) = index i xs
```

### Ordering

ByteStrings are ordered lexicographically.

```
_≤ᵇ_ : ByteString → ByteString → Bool
[] ≤ᵇ _ = true
_ ≤ᵇ [] = false
(b₁ ∷ bs₁) ≤ᵇ (b₂ ∷ bs₂) =
  (byteToNat b₁ ℕ.<ᵇ byteToNat b₂)
  ∨ ((byteToNat b₁ ℕ.≡ᵇ byteToNat b₂) ∧ (bs₁ ≤ᵇ bs₂))
```

Some tests:

```
private
  -- A byte literal; the bound is checked by computation.
  w : (n : ℕ) → {T (n ℕ.<ᵇ 2 ^ 8)} → Byte
  w n {p} = natToByte n (<ᵇ⇒< n (2 ^ 8) p)

  -- The first differing byte decides, regardless of later bytes.
  _ : (w 1 ∷ w 5 ∷ []) ≤ᵇ (w 2 ∷ w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 2 ∷ w 0 ∷ []) ≤ᵇ (w 1 ∷ w 5 ∷ []) ≡ false
  _ = refl

  -- Equal prefixes defer to the rest.
  _ : (w 1 ∷ w 2 ∷ []) ≤ᵇ (w 1 ∷ w 3 ∷ []) ≡ true
  _ = refl

  _ : (w 1 ∷ w 3 ∷ []) ≤ᵇ (w 1 ∷ w 2 ∷ []) ≡ false
  _ = refl

  -- Reflexive.
  _ : (w 7 ∷ w 255 ∷ []) ≤ᵇ (w 7 ∷ w 255 ∷ []) ≡ true
  _ = refl

  -- A proper prefix is smaller.
  _ : (w 1 ∷ []) ≤ᵇ (w 1 ∷ w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 1 ∷ w 0 ∷ []) ≤ᵇ (w 1 ∷ []) ≡ false
  _ = refl

  _ : [] ≤ᵇ (w 0 ∷ []) ≡ true
  _ = refl

  _ : (w 0 ∷ []) ≤ᵇ [] ≡ false
  _ = refl

```