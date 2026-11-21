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

## Values grouped by currency

A nested association list has an entry for each currency symbol, with the list of its
tokens and their quantities.

```
Tokens : Set
Tokens = List (TokenName × Quantity)

Nested : Set
Nested = List (CurrencySymbol × Tokens)
```

## Grouping a value by currency

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

## Flattening a grouped value

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
(x , _) <ᶠ? (y , _) = x BS.<? y

-- The stdlib has no non-emptiness predicate on lists, so we
-- define a custom one here.
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

The keys of a flattened well-formed nested list are sorted: keys with the same currency
symbol are compared by token name, and keys of later currency symbols are larger.

```
flatten-linked
  : ∀ ns → Linked _<ᶠ_ ns → All (Linked _<ᶠ_ ∘ proj₂) ns → Linked _<ᵉ_ (flatten ns)
flatten-linked []              _ _        = []
flatten-linked ((c , ts) ∷ ns) l (lt ∷ a) =
  ++-linked ts (flatten ns) lt
    (flatten-above ns (heads-above l))
    (flatten-linked ns (Linked-tail l) a)
  where
    -- The entry has a currency symbol larger than `c`.
    Above : Entry → Set
    Above ((c' , _) , _) = c BS.< c'

    heads-above
      : ∀ {ns'} → Linked _<ᶠ_ ((c , ts) ∷ ns') → All (λ (c' , _) → c BS.< c') ns'
    heads-above [-]           = []
    heads-above (r ∷ [-])     = r ∷ []
    heads-above {_ ∷ g' ∷ _} (r ∷ r' ∷ l) =
      r ∷ heads-above (BS.<-trans {c} {_} {proj₁ g'} r r' ∷ l)

    withCurrency-above : ∀ {c'} ts' → c BS.< c' → All Above (withCurrency c' ts')
    withCurrency-above []        _    = []
    withCurrency-above (_ ∷ ts') c<c' = c<c' ∷ withCurrency-above ts' c<c'

    flatten-above
      : ∀ ns' → All (λ (c' , _) → c BS.< c') ns' → All Above (flatten ns')
    flatten-above []                []          = []
    flatten-above ((_ , ts') ∷ ns') (c<c' ∷ a') =
      All.++⁺ (withCurrency-above ts' c<c') (flatten-above ns' a')

    ++-linked
      : ∀ ts' rest
      → Linked _<ᶠ_ ts' → All Above rest → Linked _<ᵉ_ rest
      → Linked _<ᵉ_ (withCurrency c ts' ++ rest)
    ++-linked []                          _       _            _          l' = l'
    ++-linked ((t , q) ∷ [])              []      _            _          _  = [-]
    ++-linked ((t , q) ∷ [])              (_ ∷ _) _            (c<c' ∷ _) l' =
      inj₁ c<c' ∷ l'
    ++-linked ((t , q) ∷ (t' , q') ∷ ts') rest    (t<t' ∷ lt') a'         l' =
      inj₂ (refl , t<t') ∷ ++-linked ((t' , q') ∷ ts') rest lt' a' l'
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
