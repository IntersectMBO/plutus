---
title: Builtin.Value.Nested.Properties
layout: page
---

This module proves that `toNested∞` and `toValue∞` are inverse: grouping the entries of
a value by currency symbol gives a well-formed nested association list, from which
`toValue∞` recovers the value, and every well-formed nested association list whose
quantities are non-zero is the grouping of a value.

```
module Builtin.Value.Nested.Properties where
```

## Imports

```
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_) renaming (tail to Linked-tail)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (recompute)

import Data.List as List
import Builtin.ByteString.Base as BS
import Builtin.ByteString.Order as BS

open import Builtin.Value.Base
open import Builtin.Value.Nested
```

## Flattening a grouped list

`group` only regroups entries, so flattening its result gives back the original list.

```
flatten-group : ∀ kvs → flatten (group kvs) ≡ kvs
flatten-group [] = refl
flatten-group (((c , t) , q) ∷ kvs) with group kvs | flatten-group kvs
... | []             | eq = cong (((c , t) , q) ∷_) eq
... | (c' , ts) ∷ ns | eq with c BS.≟ c'
...   | yes refl = cong (((c , t) , q) ∷_) eq
...   | no  _    = cong (((c , t) , q) ∷_) eq
```

## Grouping gives a well-formed nested list

Grouping a sorted list gives a well-formed nested list: its first entry `((c , t) , q)`
either joins the first currency, if that is `c`, with `t` smaller than its tokens, or
starts a new currency `c`, smaller than the others.

```
private
  -- The first group of `group kvs` starts with the first entry of `kvs`.
  data StartsWith : List Entry → Nested → Set where
    none : StartsWith [] []
    some
      : ∀ {c t q kvs ts ns}
      → StartsWith (((c , t) , q) ∷ kvs) ((c , (t , q) ∷ ts) ∷ ns)

  group-startsWith : ∀ kvs → StartsWith kvs (group kvs)
  group-startsWith [] = none
  group-startsWith (((c , t) , q) ∷ kvs) with group kvs
  ... | []            = some
  ... | (c' , _) ∷ _ with c BS.≟ c'
  ...   | yes refl = some
  ...   | no  _    = some

  replace-tokens
    : ∀ {c ts ts'} {ns : Nested}
    → Linked _<ᶠ_ ((c , ts) ∷ ns) → Linked _<ᶠ_ ((c , ts') ∷ ns)
  replace-tokens [-]     = [-]
  replace-tokens (r ∷ l) = r ∷ l

group-wellFormed : ∀ kvs → Linked _<ᵉ_ kvs → WellFormed (group kvs)
group-wellFormed [] _ = [] , []
group-wellFormed (((c , t) , q) ∷ kvs) l
  with group kvs | group-startsWith kvs | group-wellFormed kvs (Linked-tail l)
... | [] | _ | _ = [-] , ((_ ∷ _) , [-]) ∷ []
... | (c' , ts) ∷ ns | some | lc , (ne , lt) ∷ a with c BS.≟ c' | l
...   | yes refl | inj₁ c<c ∷ _       = ⊥-elim (BS.<-irrefl refl c<c)
...   | yes refl | inj₂ (_ , t<t') ∷ _ =
  replace-tokens lc , ((_ ∷ _) , t<t' ∷ lt) ∷ a
...   | no  c≢c' | inj₁ c<c' ∷ _      =
  c<c' ∷ lc , ((_ ∷ _) , [-]) ∷ (ne , lt) ∷ a
...   | no  c≢c' | inj₂ (c≡c' , _) ∷ _ = ⊥-elim (c≢c' c≡c')
```

## Recovering a value from its grouping

`toValue∞ ns` gives back a value whose entries are the flattening of `ns`, if `ns` is
well-formed. The proof that its quantities are non-zero is irrelevant in the value, so
it is recomputed.

```
toValue∞-flatten
  : ∀ ns v → WellFormed ns → Value∞.map v ≡ flatten ns → toValue∞ ns ≡ just v
toValue∞-flatten ns (mkValue∞ _ _ z) wf refl
  with wellFormed? ns | nonZero? (flatten ns)
... | yes _  | yes _  = refl
... | no ¬wf | _      = ⊥-elim (¬wf wf)
... | yes _  | no ¬nz = ⊥-elim (¬nz (recompute (nonZero? (flatten ns)) z))
```

Grouping the entries of a value gives it back.

```
toValue∞-toNested∞ : ∀ v → toValue∞ (toNested∞ v) ≡ just v
toValue∞-toNested∞ v@(mkValue∞ m s _) =
  toValue∞-flatten (group m) v
    (recompute (wellFormed? (group m)) (group-wellFormed m s))
    (sym (flatten-group m))
```

## Grouping a flattened list

Grouping the flattening of a well-formed nested list gives it back. This needs the
tokens of every currency to be non-empty, as an empty one would be lost by flattening.

```
private
  group-withCurrency
    : ∀ c t q ts rest ns
    → Linked _<ᶠ_ ((c , (t , q) ∷ ts) ∷ ns)
    → group rest ≡ ns
    → group (withCurrency c ((t , q) ∷ ts) List.++ rest) ≡ (c , (t , q) ∷ ts) ∷ ns
  group-withCurrency c t q [] rest [] _ eq rewrite eq = refl
  group-withCurrency c t q [] rest ((c' , _) ∷ _) (c<c' ∷ _) eq rewrite eq
    with c BS.≟ c'
  ... | yes refl = ⊥-elim (BS.<-irrefl refl c<c')
  ... | no  _    = refl
  group-withCurrency c t q ((t' , q') ∷ ts) rest ns l eq
    with group (withCurrency c ((t' , q') ∷ ts) List.++ rest)
       | group-withCurrency c t' q' ts rest ns (replace-tokens l) eq
  ... | _ | refl with c BS.≟ c
  ...   | yes refl = refl
  ...   | no  c≢c  = ⊥-elim (c≢c refl)

group-flatten : ∀ ns → WellFormed ns → group (flatten ns) ≡ ns
group-flatten []                       _                   = refl
group-flatten ((c , [])            ∷ ns) (_ , (() , _) ∷ _)
group-flatten ((c , (t , q) ∷ ts) ∷ ns) (l , _ ∷ a)         =
  group-withCurrency c t q ts (flatten ns) ns l (group-flatten ns (Linked-tail l , a))
```

So the value given by `toValue∞ ns` groups back to `ns`.

```
toNested∞-toValue∞ : ∀ ns {v} → toValue∞ ns ≡ just v → toNested∞ v ≡ ns
toNested∞-toValue∞ ns eq
  with wellFormed? ns | nonZero? (flatten ns)
toNested∞-toValue∞ ns refl | yes wf | yes _ = group-flatten ns wf
toNested∞-toValue∞ ns ()   | yes _  | no  _
toNested∞-toValue∞ ns ()   | no  _  | _
```
