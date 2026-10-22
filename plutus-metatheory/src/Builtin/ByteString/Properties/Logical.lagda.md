---
title: Builtin.ByteString.Properties.Logical
layout: page
---

This module proves the laws of the first batch of bitwise builtins,
[CIP-122](https://cips.cardano.org/cip/CIP-0122): the logical operations
`andByteString`, `orByteString`, `xorByteString` and `complementByteString`,
the bit accessors `readBit` and `writeBits`, and `replicateByte`.

These are exactly the properties tested by the Haskell test suite
`Evaluation.Builtins.Bitwise.CIP0122`:

* `and`, `or` and `xor` are commutative and associative under both
  semantics, the padding semantics has the empty bytestring as unit, and the
  truncation semantics has it as absorbing element;
* `and` and `or` are idempotent and distribute over themselves (on both sides
  and under both semantics), and under the truncation semantics `and`
  distributes over `or` and `xor`, and `or` over `and`;
* `xor`ing a bytestring with itself twice gives it back;
* `complement` is an involution, and De Morgan's laws hold;
* the get-set, set-get and set-set laws of `readBit` and `writeBits`, and
  `writeBits` is a homomorphism from lists of indices under concatenation to
  composition;
* `replicateByte` is a homomorphism from addition to concatenation, and every
  byte of its result is the replicated byte.

Where the Haskell suite only tests a law for one of the two semantics, it is
proved here for both whenever it holds.

```
module Builtin.ByteString.Properties.Logical where
```

## Imports

```
open import Data.Bool using (Bool; true; false; _∧_; _∨_; _xor_; not; T; if_then_else_)
import Data.Bool.Properties as BP
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ)
import Data.Integer.Properties as ℤP
import Data.List as L
import Data.List.Properties as LP
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (Maybe; just; nothing; _>>=_; map)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (does; yes; no; dec-true; dec-false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
open import Builtin.ByteString.Denotation
open import Builtin.ByteString.Properties.Byte
open import Builtin.ByteString.Properties.Base
```

## Laws of bytewise combination

The logical builtins combine their arguments byte by byte with `zipWithBS`,
which takes care of the different lengths according to the chosen semantics.
The laws are first proved for `zipWithBS` in general, from the corresponding
laws of the byte operation.

Under the truncation semantics (`pad = false`), combining with the empty
bytestring on either side gives the empty bytestring.

```
module _ {f : Byte → Byte → Byte} {u : Byte} where

  private
    Z : ByteString → ByteString → ByteString
    Z = zipWithBS f false u

    P : ByteString → ByteString → ByteString
    P = zipWithBS f true u

  zipWithBS-[]ˡ : ∀ ys → Z [] ys ≡ []
  zipWithBS-[]ˡ [] = refl
  zipWithBS-[]ˡ (y ∷ ys) = refl

  zipWithBS-[]ʳ : ∀ xs → Z xs [] ≡ []
  zipWithBS-[]ʳ [] = refl
  zipWithBS-[]ʳ (x ∷ xs) = refl
```

Under the padding semantics (`pad = true`), if the padding byte is an identity
for the byte operation then the empty bytestring is an identity.

```
  zipWithBS-identityˡ : (∀ a → f u a ≡ a) → ∀ ys → P [] ys ≡ ys
  zipWithBS-identityˡ id [] = refl
  zipWithBS-identityˡ id (y ∷ ys) = cong₂ _∷_ (id y) (zipWithBS-identityˡ id ys)

  zipWithBS-identityʳ : (∀ a → f a u ≡ a) → ∀ xs → P xs [] ≡ xs
  zipWithBS-identityʳ id [] = refl
  zipWithBS-identityʳ id (x ∷ xs) = cong₂ _∷_ (id x) (zipWithBS-identityʳ id xs)
```

Commutativity, under either semantics.

```
  zipWithBS-comm
    : (∀ a b → f a b ≡ f b a)
    → ∀ pad xs ys → zipWithBS f pad u xs ys ≡ zipWithBS f pad u ys xs
  zipWithBS-comm c pad [] [] = refl
  zipWithBS-comm c false [] (y ∷ ys) = refl
  zipWithBS-comm c true [] (y ∷ ys) = cong₂ _∷_ (c u y) (zipWithBS-comm c true [] ys)
  zipWithBS-comm c false (x ∷ xs) [] = refl
  zipWithBS-comm c true (x ∷ xs) [] = cong₂ _∷_ (c x u) (zipWithBS-comm c true xs [])
  zipWithBS-comm c pad (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (c x y) (zipWithBS-comm c pad xs ys)
```

Associativity. Under the truncation semantics an empty argument makes both
sides empty; under the padding semantics it disappears from both sides, which
requires the padding byte to be an identity.

```
  zipWithBS-assoc-trunc
    : (∀ a b c → f (f a b) c ≡ f a (f b c))
    → ∀ xs ys zs → Z (Z xs ys) zs ≡ Z xs (Z ys zs)
  zipWithBS-assoc-trunc a [] ys zs =
    trans (cong (λ w → Z w zs) (zipWithBS-[]ˡ ys))
          (trans (zipWithBS-[]ˡ zs) (sym (zipWithBS-[]ˡ (Z ys zs))))
  zipWithBS-assoc-trunc a (x ∷ xs) [] zs =
    trans (zipWithBS-[]ˡ zs) (cong (Z (x ∷ xs)) (sym (zipWithBS-[]ˡ zs)))
  zipWithBS-assoc-trunc a (x ∷ xs) (y ∷ ys) [] = refl
  zipWithBS-assoc-trunc a (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (a x y z) (zipWithBS-assoc-trunc a xs ys zs)

  zipWithBS-assoc-pad
    : (∀ a b c → f (f a b) c ≡ f a (f b c))
    → (∀ a → f u a ≡ a) → (∀ a → f a u ≡ a)
    → ∀ xs ys zs → P (P xs ys) zs ≡ P xs (P ys zs)
  zipWithBS-assoc-pad a idˡ idʳ [] ys zs =
    trans (cong (λ w → P w zs) (zipWithBS-identityˡ idˡ ys))
          (sym (zipWithBS-identityˡ idˡ (P ys zs)))
  zipWithBS-assoc-pad a idˡ idʳ (x ∷ xs) [] zs =
    trans (cong (λ w → P w zs) (zipWithBS-identityʳ idʳ (x ∷ xs)))
          (cong (P (x ∷ xs)) (sym (zipWithBS-identityˡ idˡ zs)))
  zipWithBS-assoc-pad a idˡ idʳ (x ∷ xs) (y ∷ ys) [] =
    trans (zipWithBS-identityʳ idʳ (P (x ∷ xs) (y ∷ ys)))
          (cong (P (x ∷ xs)) (sym (zipWithBS-identityʳ idʳ (y ∷ ys))))
  zipWithBS-assoc-pad a idˡ idʳ (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (a x y z) (zipWithBS-assoc-pad a idˡ idʳ xs ys zs)
```

Idempotence, and the law `x ∙ (x ∙ x) = x` satisfied by `xor`, under either
semantics: both only ever combine bytestrings with themselves.

```
  zipWithBS-idem : (∀ a → f a a ≡ a) → ∀ pad xs → zipWithBS f pad u xs xs ≡ xs
  zipWithBS-idem i pad [] = refl
  zipWithBS-idem i pad (x ∷ xs) = cong₂ _∷_ (i x) (zipWithBS-idem i pad xs)

  zipWithBS-involute
    : (∀ a → f a (f a a) ≡ a)
    → ∀ pad xs → zipWithBS f pad u xs (zipWithBS f pad u xs xs) ≡ xs
  zipWithBS-involute i pad [] = refl
  zipWithBS-involute i pad (x ∷ xs) = cong₂ _∷_ (i x) (zipWithBS-involute i pad xs)
```

Under the truncation semantics, distributivity of one byte operation over
another lifts to bytestrings: if any argument is empty, both sides are empty.

```
module _ {f g : Byte → Byte → Byte} {u v : Byte} where

  private
    F : ByteString → ByteString → ByteString
    F = zipWithBS f false u

    G : ByteString → ByteString → ByteString
    G = zipWithBS g false v

  zipWithBS-distribˡ-trunc
    : (∀ a b c → f a (g b c) ≡ g (f a b) (f a c))
    → ∀ xs ys zs → F xs (G ys zs) ≡ G (F xs ys) (F xs zs)
  zipWithBS-distribˡ-trunc d [] ys zs =
    trans (zipWithBS-[]ˡ (G ys zs))
          (sym (cong₂ G (zipWithBS-[]ˡ ys) (zipWithBS-[]ˡ zs)))
  zipWithBS-distribˡ-trunc d (x ∷ xs) [] zs =
    trans (cong (F (x ∷ xs)) (zipWithBS-[]ˡ zs)) (sym (zipWithBS-[]ˡ (F (x ∷ xs) zs)))
  zipWithBS-distribˡ-trunc d (x ∷ xs) (y ∷ ys) [] = refl
  zipWithBS-distribˡ-trunc d (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (d x y z) (zipWithBS-distribˡ-trunc d xs ys zs)
```

Mapping a byte homomorphism over combined bytestrings. This gives De Morgan's
laws, where the padding byte of `and` (`255B`) is the complement of that of
`or` (`0B`).

```
mapBS-zipWithBS
  : ∀ {h f g} {u} → (∀ a b → h (f a b) ≡ g (h a) (h b))
  → ∀ pad xs ys → mapBS h (zipWithBS f pad u xs ys) ≡ zipWithBS g pad (h u) (mapBS h xs) (mapBS h ys)
mapBS-zipWithBS c pad [] [] = refl
mapBS-zipWithBS c false [] (y ∷ ys) = refl
mapBS-zipWithBS {u = u} c true [] (y ∷ ys) = cong₂ _∷_ (c u y) (mapBS-zipWithBS c true [] ys)
mapBS-zipWithBS c false (x ∷ xs) [] = refl
mapBS-zipWithBS {u = u} c true (x ∷ xs) [] = cong₂ _∷_ (c x u) (mapBS-zipWithBS c true xs [])
mapBS-zipWithBS c pad (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (c x y) (mapBS-zipWithBS c pad xs ys)

mapBS-involutive : ∀ {h} → (∀ a → h (h a) ≡ a) → ∀ xs → mapBS h (mapBS h xs) ≡ xs
mapBS-involutive i [] = refl
mapBS-involutive i (x ∷ xs) = cong₂ _∷_ (i x) (mapBS-involutive i xs)
```

### Distributivity in a semilattice

An operation that is commutative, associative and idempotent distributes over
itself on both sides. This gives the self-distributivity of `and` and `or`
under both semantics, without a separate induction.

```
module Semilattice
  (_∙_ : ByteString → ByteString → ByteString)
  (comm : ∀ x y → x ∙ y ≡ y ∙ x)
  (assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z))
  (idem : ∀ x → x ∙ x ≡ x)
  where

  distribˡ : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
  distribˡ x y z = sym (begin
    (x ∙ y) ∙ (x ∙ z)
    ≡⟨ assoc x y (x ∙ z) ⟩
    x ∙ (y ∙ (x ∙ z))
    ≡⟨ cong (x ∙_) (assoc y x z) ⟨
    x ∙ ((y ∙ x) ∙ z)
    ≡⟨ cong (λ w → x ∙ (w ∙ z)) (comm y x) ⟩
    x ∙ ((x ∙ y) ∙ z)
    ≡⟨ cong (x ∙_) (assoc x y z) ⟩
    x ∙ (x ∙ (y ∙ z))
    ≡⟨ assoc x x (y ∙ z) ⟨
    (x ∙ x) ∙ (y ∙ z)
    ≡⟨ cong (_∙ (y ∙ z)) (idem x) ⟩
    x ∙ (y ∙ z)
    ∎)

  distribʳ : ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)
  distribʳ x y z = begin
    (x ∙ y) ∙ z
    ≡⟨ comm (x ∙ y) z ⟩
    z ∙ (x ∙ y)
    ≡⟨ distribˡ z x y ⟩
    (z ∙ x) ∙ (z ∙ y)
    ≡⟨ cong₂ _∙_ (comm z x) (comm z y) ⟩
    (x ∙ z) ∙ (y ∙ z)
    ∎
```

## andByteString

```
and-comm : ∀ pad xs ys → andBYTESTRING pad xs ys ≡ andBYTESTRING pad ys xs
and-comm = zipWithBS-comm (zipByte-comm BP.∧-comm)

and-assoc
  : ∀ pad xs ys zs
  → andBYTESTRING pad (andBYTESTRING pad xs ys) zs ≡ andBYTESTRING pad xs (andBYTESTRING pad ys zs)
and-assoc false = zipWithBS-assoc-trunc (zipByte-assoc BP.∧-assoc)
and-assoc true =
  zipWithBS-assoc-pad (zipByte-assoc BP.∧-assoc)
    (zipByte-identityˡ BP.∧-identityˡ) (zipByte-identityʳ BP.∧-identityʳ)

and-idem : ∀ pad xs → andBYTESTRING pad xs xs ≡ xs
and-idem = zipWithBS-idem (zipByte-idem BP.∧-idem)

and-identityˡ-pad : ∀ xs → andBYTESTRING true [] xs ≡ xs
and-identityˡ-pad = zipWithBS-identityˡ (zipByte-identityˡ BP.∧-identityˡ)

and-identityʳ-pad : ∀ xs → andBYTESTRING true xs [] ≡ xs
and-identityʳ-pad = zipWithBS-identityʳ (zipByte-identityʳ BP.∧-identityʳ)

and-zeroˡ-trunc : ∀ xs → andBYTESTRING false [] xs ≡ []
and-zeroˡ-trunc = zipWithBS-[]ˡ

and-zeroʳ-trunc : ∀ xs → andBYTESTRING false xs [] ≡ []
and-zeroʳ-trunc = zipWithBS-[]ʳ

and-distribˡ-and
  : ∀ pad xs ys zs
  → andBYTESTRING pad xs (andBYTESTRING pad ys zs)
    ≡ andBYTESTRING pad (andBYTESTRING pad xs ys) (andBYTESTRING pad xs zs)
and-distribˡ-and pad = Semilattice.distribˡ (andBYTESTRING pad) (and-comm pad) (and-assoc pad) (and-idem pad)

and-distribʳ-and
  : ∀ pad xs ys zs
  → andBYTESTRING pad (andBYTESTRING pad xs ys) zs
    ≡ andBYTESTRING pad (andBYTESTRING pad xs zs) (andBYTESTRING pad ys zs)
and-distribʳ-and pad = Semilattice.distribʳ (andBYTESTRING pad) (and-comm pad) (and-assoc pad) (and-idem pad)

and-distribˡ-or-trunc
  : ∀ xs ys zs
  → andBYTESTRING false xs (orBYTESTRING false ys zs)
    ≡ orBYTESTRING false (andBYTESTRING false xs ys) (andBYTESTRING false xs zs)
and-distribˡ-or-trunc = zipWithBS-distribˡ-trunc (zipByte-distribˡ BP.∧-distribˡ-∨)

and-distribˡ-xor-trunc
  : ∀ xs ys zs
  → andBYTESTRING false xs (xorBYTESTRING false ys zs)
    ≡ xorBYTESTRING false (andBYTESTRING false xs ys) (andBYTESTRING false xs zs)
and-distribˡ-xor-trunc = zipWithBS-distribˡ-trunc (zipByte-distribˡ BP.∧-distribˡ-xor)
```

## orByteString

```
or-comm : ∀ pad xs ys → orBYTESTRING pad xs ys ≡ orBYTESTRING pad ys xs
or-comm = zipWithBS-comm (zipByte-comm BP.∨-comm)

or-assoc
  : ∀ pad xs ys zs
  → orBYTESTRING pad (orBYTESTRING pad xs ys) zs ≡ orBYTESTRING pad xs (orBYTESTRING pad ys zs)
or-assoc false = zipWithBS-assoc-trunc (zipByte-assoc BP.∨-assoc)
or-assoc true =
  zipWithBS-assoc-pad (zipByte-assoc BP.∨-assoc)
    (zipByte-identityˡ BP.∨-identityˡ) (zipByte-identityʳ BP.∨-identityʳ)

or-idem : ∀ pad xs → orBYTESTRING pad xs xs ≡ xs
or-idem = zipWithBS-idem (zipByte-idem BP.∨-idem)

or-identityˡ-pad : ∀ xs → orBYTESTRING true [] xs ≡ xs
or-identityˡ-pad = zipWithBS-identityˡ (zipByte-identityˡ BP.∨-identityˡ)

or-identityʳ-pad : ∀ xs → orBYTESTRING true xs [] ≡ xs
or-identityʳ-pad = zipWithBS-identityʳ (zipByte-identityʳ BP.∨-identityʳ)

or-zeroˡ-trunc : ∀ xs → orBYTESTRING false [] xs ≡ []
or-zeroˡ-trunc = zipWithBS-[]ˡ

or-zeroʳ-trunc : ∀ xs → orBYTESTRING false xs [] ≡ []
or-zeroʳ-trunc = zipWithBS-[]ʳ

or-distribˡ-or
  : ∀ pad xs ys zs
  → orBYTESTRING pad xs (orBYTESTRING pad ys zs)
    ≡ orBYTESTRING pad (orBYTESTRING pad xs ys) (orBYTESTRING pad xs zs)
or-distribˡ-or pad = Semilattice.distribˡ (orBYTESTRING pad) (or-comm pad) (or-assoc pad) (or-idem pad)

or-distribʳ-or
  : ∀ pad xs ys zs
  → orBYTESTRING pad (orBYTESTRING pad xs ys) zs
    ≡ orBYTESTRING pad (orBYTESTRING pad xs zs) (orBYTESTRING pad ys zs)
or-distribʳ-or pad = Semilattice.distribʳ (orBYTESTRING pad) (or-comm pad) (or-assoc pad) (or-idem pad)

or-distribˡ-and-trunc
  : ∀ xs ys zs
  → orBYTESTRING false xs (andBYTESTRING false ys zs)
    ≡ andBYTESTRING false (orBYTESTRING false xs ys) (orBYTESTRING false xs zs)
or-distribˡ-and-trunc = zipWithBS-distribˡ-trunc (zipByte-distribˡ BP.∨-distribˡ-∧)
```

## xorByteString

```
xor-comm : ∀ pad xs ys → xorBYTESTRING pad xs ys ≡ xorBYTESTRING pad ys xs
xor-comm = zipWithBS-comm (zipByte-comm BP.xor-comm)

xor-assoc
  : ∀ pad xs ys zs
  → xorBYTESTRING pad (xorBYTESTRING pad xs ys) zs ≡ xorBYTESTRING pad xs (xorBYTESTRING pad ys zs)
xor-assoc false = zipWithBS-assoc-trunc (zipByte-assoc BP.xor-assoc)
xor-assoc true =
  zipWithBS-assoc-pad (zipByte-assoc BP.xor-assoc)
    (zipByte-identityˡ BP.xor-identityˡ) (zipByte-identityʳ BP.xor-identityʳ)

xor-identityˡ-pad : ∀ xs → xorBYTESTRING true [] xs ≡ xs
xor-identityˡ-pad = zipWithBS-identityˡ (zipByte-identityˡ BP.xor-identityˡ)

xor-identityʳ-pad : ∀ xs → xorBYTESTRING true xs [] ≡ xs
xor-identityʳ-pad = zipWithBS-identityʳ (zipByte-identityʳ BP.xor-identityʳ)

xor-zeroˡ-trunc : ∀ xs → xorBYTESTRING false [] xs ≡ []
xor-zeroˡ-trunc = zipWithBS-[]ˡ

xor-zeroʳ-trunc : ∀ xs → xorBYTESTRING false xs [] ≡ []
xor-zeroʳ-trunc = zipWithBS-[]ʳ

xor-involute : ∀ pad xs → xorBYTESTRING pad xs (xorBYTESTRING pad xs xs) ≡ xs
xor-involute = zipWithBS-involute (zipByte-involute λ a → trans (cong (a xor_) (BP.xor-same a)) (BP.xor-identityʳ a))
```

`xor`ing a bytestring with itself clears every bit.

```
xor-self : ∀ pad xs → xorBYTESTRING pad xs xs ≡ replicateBS (lengthℕ xs) 0B
xor-self pad [] = refl
xor-self pad (x ∷ xs) = cong₂ _∷_ (zipByte-diag BP.xor-same x) (xor-self pad xs)
```

## complementByteString

De Morgan's laws for booleans.

```
private

  not-∧ : ∀ a b → not (a ∧ b) ≡ not a ∨ not b
  not-∧ true b = refl
  not-∧ false b = refl

  not-∨ : ∀ a b → not (a ∨ b) ≡ not a ∧ not b
  not-∨ true b = refl
  not-∨ false b = refl
```

```
complement-involutive : ∀ xs → complementBYTESTRING (complementBYTESTRING xs) ≡ xs
complement-involutive = mapBS-involutive (mapByte-involutive BP.not-involutive)

complement-and
  : ∀ pad xs ys
  → complementBYTESTRING (andBYTESTRING pad xs ys)
    ≡ orBYTESTRING pad (complementBYTESTRING xs) (complementBYTESTRING ys)
complement-and = mapBS-zipWithBS (mapByte-zipByte not-∧)

complement-or
  : ∀ pad xs ys
  → complementBYTESTRING (orBYTESTRING pad xs ys)
    ≡ andBYTESTRING pad (complementBYTESTRING xs) (complementBYTESTRING ys)
complement-or = mapBS-zipWithBS (mapByte-zipByte not-∨)
```

## readBit and writeBits

Validity of a list of indices distributes over concatenation.

```
private

  all-++ : ∀ {A : Set} (p : A → Bool) xs ys → all p (xs L.++ ys) ≡ all p xs ∧ all p ys
  all-++ p L.[] ys = refl
  all-++ p (x L.∷ xs) ys = trans (cong (p x ∧_) (all-++ p xs ys)) (sym (BP.∧-assoc (p x) (all p xs) (all p ys)))
```

Writing to a bytestring and then writing to the result is the same as
applying both batches of updates to the original bit view, provided all the
indices are valid; otherwise both fail. The second batch is checked against
the result of the first, which has the same length.

```
writeBITS-bind
  : ∀ bs ixs₁ ixs₂ u v
  → (writeBITS bs ixs₁ u >>= λ bs' → writeBITS bs' ixs₂ v)
    ≡ (if all (validBitIndex (bitLength bs)) (ixs₁ L.++ ixs₂)
       then just (fromBits (setBits ixs₂ v (setBits ixs₁ u (toBits bs))))
       else nothing)
writeBITS-bind bs ixs₁ ixs₂ u v
  rewrite all-++ (validBitIndex (bitLength bs)) ixs₁ ixs₂
  with all (validBitIndex (bitLength bs)) ixs₁ in valid₁
... | false = refl
... | true
  with all (validBitIndex (bitLength bs)) ixs₂ in valid₂
... | false = writeBITS-invalid (written bs ixs₁ u) ixs₂ v
               (trans (cong (λ n → all (validBitIndex n) ixs₂) (bitLength-written bs ixs₁ u)) valid₂)
... | true = trans (writeBITS-valid (written bs ixs₁ u) ixs₂ v
                     (trans (cong (λ n → all (validBitIndex n) ixs₂) (bitLength-written bs ixs₁ u)) valid₂))
                   (cong (λ bits → just (fromBits (setBits ixs₂ v bits))) (toBits-written bs ixs₁ u))
```

If you read a bit and write the same value back to the same index, nothing
changes.

```
get-set : ∀ bs i u → readBIT bs i ≡ just u → writeBITS bs (i L.∷ L.[]) u ≡ just bs
get-set bs (+ i) u read≡ =
  trans (writeBITS-valid bs (+ i L.∷ L.[]) u
          (cong (_∧ true) (validBitIndex-+ bs i i<len)))
        (cong just (trans (cong fromBits (setBit-lookupBit i u (toBits bs) lookup≡))
                          (fromBits-toBits bs)))
  where
    lookup≡ = trans (sym (readBIT-lookupBit bs i)) read≡
    i<len = ℕP.<-≤-trans (lookupBit-just-< (toBits bs) i lookup≡) (ℕP.≤-reflexive (length-toBits bs))
```

If you write a bit and read it back, you get what you wrote.

```
set-get
  : ∀ bs i u → i < lengthℕ bs * 8
  → (writeBITS bs (+ i L.∷ L.[]) u >>= λ bs' → readBIT bs' (+ i)) ≡ just u
set-get bs i u i<len
  rewrite writeBITS-valid bs (+ i L.∷ L.[]) u (cong (_∧ true) (validBitIndex-+ bs i i<len))
  = begin
    readBIT (written bs (+ i L.∷ L.[]) u) (+ i)
    ≡⟨ readBIT-lookupBit (written bs (+ i L.∷ L.[]) u) i ⟩
    lookupBit (toBits (written bs (+ i L.∷ L.[]) u)) i
    ≡⟨ cong (λ bits → lookupBit bits i) (toBits-written bs (+ i L.∷ L.[]) u) ⟩
    lookupBit (setBit i u (toBits bs)) i
    ≡⟨ lookupBit-setBit-≡ i u (toBits bs) (ℕP.<-≤-trans i<len (ℕP.≤-reflexive (sym (length-toBits bs)))) ⟩
    just u
    ∎
```

If you write twice to the same index, the second write wins.

```
set-set
  : ∀ bs i u v
  → (writeBITS bs (i L.∷ i L.∷ L.[]) u >>= λ bs' → writeBITS bs' (i L.∷ i L.∷ L.[]) v)
    ≡ writeBITS bs (i L.∷ L.[]) v
set-set bs i u v
  rewrite writeBITS-bind bs (i L.∷ i L.∷ L.[]) (i L.∷ i L.∷ L.[]) u v
  with validBitIndex (bitLength bs) i in valid
... | false = refl
... | true = cong (λ bits → just (fromBits bits)) lemma
  where
    j = ℤ.∣ i ∣
    bits = toBits bs
    lemma : setBit j v (setBit j v (setBit j u (setBit j u bits))) ≡ setBit j v bits
    lemma = trans (setBit-setBit j v v _) (trans (setBit-setBit j v u _) (setBit-setBit j v u bits))
```

Writing with no indices changes nothing, and writing the same value at two
lists of indices in turn is writing it at their concatenation. Since all the
writes set the same value, their order does not matter.

```
writeBITS-[] : ∀ bs u → writeBITS bs L.[] u ≡ just bs
writeBITS-[] bs u = cong just (fromBits-toBits bs)

private

  setBit-setBits : ∀ i ixs u bits → setBit i u (setBits ixs u bits) ≡ setBits ixs u (setBit i u bits)
  setBit-setBits i L.[] u bits = refl
  setBit-setBits i (j L.∷ ixs) u bits =
    trans (setBit-comm i ℤ.∣ j ∣ u _) (cong (setBit ℤ.∣ j ∣ u) (setBit-setBits i ixs u bits))

  setBits-comm
    : ∀ ixs₁ ixs₂ u bits
    → setBits ixs₂ u (setBits ixs₁ u bits) ≡ setBits ixs₁ u (setBits ixs₂ u bits)
  setBits-comm L.[] ixs₂ u bits = refl
  setBits-comm (i L.∷ ixs₁) ixs₂ u bits =
    trans (sym (setBit-setBits-gen ixs₂))
          (cong (setBit ℤ.∣ i ∣ u) (setBits-comm ixs₁ ixs₂ u bits))
    where
      setBit-setBits-gen
        : ∀ ixs → setBit ℤ.∣ i ∣ u (setBits ixs u (setBits ixs₁ u bits))
                ≡ setBits ixs u (setBit ℤ.∣ i ∣ u (setBits ixs₁ u bits))
      setBit-setBits-gen ixs = setBit-setBits ℤ.∣ i ∣ ixs u (setBits ixs₁ u bits)

  setBits-++ : ∀ ixs₁ ixs₂ u bits → setBits (ixs₁ L.++ ixs₂) u bits ≡ setBits ixs₁ u (setBits ixs₂ u bits)
  setBits-++ ixs₁ ixs₂ u bits = LP.foldr-++ (λ i → setBit ℤ.∣ i ∣ u) bits ixs₁ ixs₂

writeBITS-++
  : ∀ bs ixs₁ ixs₂ u
  → (writeBITS bs ixs₁ u >>= λ bs' → writeBITS bs' ixs₂ u) ≡ writeBITS bs (ixs₁ L.++ ixs₂) u
writeBITS-++ bs ixs₁ ixs₂ u
  rewrite writeBITS-bind bs ixs₁ ixs₂ u u
        | setBits-comm ixs₁ ixs₂ u (toBits bs)
        | sym (setBits-++ ixs₁ ixs₂ u (toBits bs))
  = refl
```

## replicateByte

Replicating a valid byte value succeeds for every length in `[0, 8192]`.

```
private

  T⇒≡true : ∀ {b} → T b → b ≡ true
  T⇒≡true {true} _ = refl

replicateBYTE-valid
  : ∀ n k → n ≤ 8192 → k < 256 → replicateBYTE (+ n) (+ k) ≡ just (replicateBS n (ℕToByte k))
replicateBYTE-valid n k n≤ k<
  with toByte (+ k) | toByte-valid k k<
... | .(just (ℕToByte k)) | refl rewrite T⇒≡true (ℕP.≤⇒≤ᵇ n≤) = refl

replicateBYTE-invalid : ∀ l w → toByte w ≡ nothing → replicateBYTE l w ≡ nothing
replicateBYTE-invalid l w invalid with toByte w
replicateBYTE-invalid l w refl | nothing = refl
```

Replicating zero times gives the empty bytestring, and replication turns
addition into concatenation. If the byte value is invalid, both sides of the
second law fail.

```
replicateBYTE-zero : ∀ k → k < 256 → replicateBYTE 0ℤ (+ k) ≡ just []
replicateBYTE-zero k k< = replicateBYTE-valid 0 k z≤n k<

replicateBYTE-+
  : ∀ m n w → m + n ≤ 8192
  → (replicateBYTE (+ m) w >>= λ xs → replicateBYTE (+ n) w >>= λ ys → just (concat xs ys))
    ≡ replicateBYTE (+ (m + n)) w
replicateBYTE-+ m n w m+n≤ with toByte w
... | nothing = refl
... | just b
  rewrite T⇒≡true (ℕP.≤⇒≤ᵇ (ℕP.≤-trans (ℕP.m≤m+n m n) m+n≤))
        | T⇒≡true (ℕP.≤⇒≤ᵇ (ℕP.≤-trans (ℕP.m≤n+m n m) m+n≤))
        | T⇒≡true (ℕP.≤⇒≤ᵇ m+n≤)
  = cong just (trans (concat≡++ᵇ (replicateBS m b) (replicateBS n b)) (replicateBS-+ m n b))
```

Every byte of a replicated bytestring is the replicated byte. `indexFrom`
looks a byte up by its position, counting from its second argument.

```
private

  nth : ByteString → ℕ → Maybe Byte
  nth [] _ = nothing
  nth (x ∷ xs) zero = just x
  nth (x ∷ xs) (suc i) = nth xs i

  indexFrom-nth : ∀ bs j i → indexFrom (+ (j + i)) (+ j) bs ≡ nth bs i
  indexFrom-nth [] j i = refl
  indexFrom-nth (x ∷ xs) j zero
    rewrite dec-true (+ j ℤ.≟ + (j + 0)) (cong +_ (sym (ℕP.+-identityʳ j))) = refl
  indexFrom-nth (x ∷ xs) j (suc i)
    rewrite dec-false (+ j ℤ.≟ + (j + suc i)) (λ eq → ℕP.m≢1+m+n j (trans (ℤP.+-injective eq) (ℕP.+-suc j i)))
    = trans (cong (λ k → indexFrom (+ k) (+ (j + 1)) xs) (sym (ℕP.+-assoc j 1 i)))
            (indexFrom-nth xs (j + 1) i)

  nth-replicate : ∀ n b i → i < n → nth (replicateBS n b) i ≡ just b
  nth-replicate (suc n) b zero _ = refl
  nth-replicate (suc n) b (suc i) (s≤s i<n) = nth-replicate n b i i<n

index-replicate : ∀ n b i → i < n → index (replicateBS n b) (+ i) ≡ just (byteToℤ b)
index-replicate n b i i<n
  rewrite indexFrom-nth (replicateBS n b) 0 i
        | nth-replicate n b i i<n
  = refl

replicateBYTE-index
  : ∀ n k i → n ≤ 8192 → k < 256 → i < n
  → (replicateBYTE (+ n) (+ k) >>= λ bs → index bs (+ i)) ≡ just (+ k)
replicateBYTE-index n k i n≤ k< i<n
  rewrite replicateBYTE-valid n k n≤ k<
        | index-replicate n (ℕToByte k) i i<n
        | byteToℕ-ℕToByte k k<
  = refl
```
