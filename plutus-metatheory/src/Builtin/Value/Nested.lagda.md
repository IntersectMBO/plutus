---
title: Builtin.Value.Nested
layout: page
---

This module relates `Value∞` to the nested association lists used to encode values, for
example as `Data`: a list of currency symbols, each with the list of its tokens and their
quantities.

```
module Builtin.Value.Nested where
```

## Imports

```
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All
  using (All; []; _∷_; all?) renaming (map to All-map)
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_; linked?) renaming (tail to Linked-tail)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_∘_; _on_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no; _×-dec_)

import Data.List as List
import Data.List.Relation.Unary.All.Properties as All
import Builtin.ByteString.Base as BS
import Builtin.ByteString.Order as BS

open import Builtin.ByteString.Base using (ByteString)
open import Builtin.Value.Base
```

## Nested association lists

A nested association list has an entry for each currency symbol, with the list of its
tokens and their quantities.

```
Tokens : Set
Tokens = List (TokenName × Quantity)

Nested : Set
Nested = List (CurrencySymbol × Tokens)
```

## From values

`group kvs` groups the entries of `kvs` by currency symbol. In a well-formed list the
entries of each currency are next to each other, so it only compares neighbouring
currency symbols.

```
group : List Entry → Nested
group [] = []
group (((c , t) , q) ∷ kvs) with group kvs
... | [] = (c , (t , q) ∷ []) ∷ []
... | (c' , ts) ∷ ns with c BS.≟ c'
...   | yes _ = (c , (t , q) ∷ ts) ∷ ns
...   | no  _ = (c , (t , q) ∷ []) ∷ (c' , ts) ∷ ns

toNested∞ : Value∞ → Nested
toNested∞ = group ∘ Value∞.map
```

## To values

`flatten ns` is the flat list of the entries of `ns`.

```
withCurrency : CurrencySymbol → Tokens → List Entry
withCurrency c = List.map λ (t , q) → (c , t) , q

flatten : Nested → List Entry
flatten []              = []
flatten ((c , ts) ∷ ns) = withCurrency c ts ++ flatten ns
```

A nested association list is *well-formed* when its currency symbols are strictly
increasing, and the tokens of every currency are non-empty and strictly increasing.
Well-formedness is decidable.

```
-- Comparison by first component, of both currencies and tokens.
_<ᶠ_ : ∀ {A : Set} → ByteString × A → ByteString × A → Set
_<ᶠ_ = BS._<_ on proj₁

_<ᶠ?_ : ∀ {A : Set} (x y : ByteString × A) → Dec (x <ᶠ y)
x <ᶠ? y = proj₁ x BS.<? proj₁ y

data NonEmpty {A : Set} : List A → Set where
  _∷_ : ∀ x xs → NonEmpty (x ∷ xs)

nonEmpty? : ∀ {A : Set} (xs : List A) → Dec (NonEmpty xs)
nonEmpty? []       = no λ ()
nonEmpty? (x ∷ xs) = yes (x ∷ xs)

WellFormedTokens : Tokens → Set
WellFormedTokens ts = NonEmpty ts × Linked _<ᶠ_ ts

WellFormed : Nested → Set
WellFormed ns = Linked _<ᶠ_ ns × All (WellFormedTokens ∘ proj₂) ns

wellFormed? : ∀ ns → Dec (WellFormed ns)
wellFormed? ns =
  linked? _<ᶠ?_ ns ×-dec all? (λ (_ , ts) → nonEmpty? ts ×-dec linked? _<ᶠ?_ ts) ns
```

The keys of a flattened well-formed nested list are sorted. The keys with the same
currency symbol are compared by token name, and those of later currency symbols are
larger, since they compare greater on their currency symbol. Sortedness does not need
the tokens to be non-empty, which only matters to rule out empty inner lists, as the
builtin does.

```
private
  -- The currency symbol of an entry.
  cur : Entry → CurrencySymbol
  cur = proj₁ ∘ proj₁

  withCurrency-above
    : ∀ {c c'} ts → c BS.< c' → All (λ e → c BS.< cur e) (withCurrency c' ts)
  withCurrency-above []       _     = []
  withCurrency-above (_ ∷ ts) c<c' = c<c' ∷ withCurrency-above ts c<c'

  flatten-above
    : ∀ {c} ns → All (λ g → c BS.< proj₁ g) ns → All (λ e → c BS.< cur e) (flatten ns)
  flatten-above []              []          = []
  flatten-above ((_ , ts) ∷ ns) (c<c' ∷ a) =
    All.++⁺ (withCurrency-above ts c<c') (flatten-above ns a)

  -- The currency symbols after the first one of a sorted list are larger.
  heads-above
    : ∀ {g : CurrencySymbol × Tokens} {ns}
    → Linked _<ᶠ_ (g ∷ ns) → All (λ g' → proj₁ g BS.< proj₁ g') ns
  heads-above [-]           = []
  heads-above (r ∷ [-])     = r ∷ []
  heads-above {g} {g' ∷ g'' ∷ _} (r ∷ r' ∷ l) =
    r ∷ heads-above {g} (BS.<-trans {proj₁ g} {proj₁ g'} {proj₁ g''} r r' ∷ l)

  withCurrency-++-linked
    : ∀ c ts rest
    → Linked _<ᶠ_ ts
    → All (λ e → c BS.< cur e) rest
    → Linked _<ᵉ_ rest
    → Linked _<ᵉ_ (withCurrency c ts ++ rest)
  withCurrency-++-linked c []                      rest _          _          l = l
  withCurrency-++-linked c ((t , q) ∷ [])          []   _          _          _ = [-]
  withCurrency-++-linked c ((t , q) ∷ [])          (_ ∷ _) _       (c<c' ∷ _) l =
    inj₁ c<c' ∷ l
  withCurrency-++-linked c ((t , q) ∷ (t' , q') ∷ ts) rest (t<t' ∷ lt) a l =
    inj₂ (refl , t<t') ∷ withCurrency-++-linked c ((t' , q') ∷ ts) rest lt a l

flatten-linked
  : ∀ ns → Linked _<ᶠ_ ns → All (Linked _<ᶠ_ ∘ proj₂) ns → Linked _<ᵉ_ (flatten ns)
flatten-linked []              _ _        = []
flatten-linked ((c , ts) ∷ ns) l (lt ∷ a) =
  withCurrency-++-linked c ts (flatten ns) lt
    (flatten-above ns (heads-above l))
    (flatten-linked ns (Linked-tail l) a)
```

`toValue∞ ns` checks that `ns` is well-formed and that its quantities are non-zero, and
gives the corresponding `Value∞`.

```
toValue∞ : Nested → Maybe Value∞
toValue∞ ns with wellFormed? ns | nonZero? (flatten ns)
... | yes (l , a) | yes nz =
  just (mkValue∞ (flatten ns) (flatten-linked ns l (All-map proj₂ a)) nz)
... | _           | _      = nothing
```
