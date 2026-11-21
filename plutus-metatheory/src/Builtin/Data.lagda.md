---
title: Builtin.Data
layout: page
---

This module defines the builtin type `Data` and the builtins that build, inspect and
compare it.

```
module Builtin.Data where
```

## Imports

```
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_; -_)
open import Data.Nat using (s≤s; z≤n)
open import Data.Unit using (⊤)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; isYes)

import Data.Integer as ℤ
import Data.List as L
import Builtin.ByteString.Base as BS

open import Builtin.Binary using (natToByte)
open import Builtin.ByteString.Base using (ByteString)
```

## Data

`Data` is a tree, whose leaves are integers and bytestrings, and whose nodes are lists,
association lists, and constructor applications, tagged with an integer. It is used to
pass arbitrary data, such as the datums and redeemers of scripts, to and from scripts.

```
data Data : Set where
  Constr : ℤ → L.List Data → Data
  Map    : L.List (Data × Data) → Data
  List   : L.List Data → Data
  I      : ℤ → Data
  B      : ByteString → Data
```

## Equality

Equality of `Data` is decidable. It is defined together with equality of the lists that
`Data` contains, so that every recursive call is on a subterm.

```
_≟_   : DecidableEquality Data
_≟ˡ_  : DecidableEquality (L.List Data)
_≟ᵐ_  : DecidableEquality (L.List (Data × Data))

Constr i ds ≟ Constr j es with i ℤ.≟ j | ds ≟ˡ es
... | yes refl | yes refl = yes refl
... | no  i≢j  | _        = no λ { refl → i≢j refl }
... | yes _    | no  ds≢es = no λ { refl → ds≢es refl }
Map ps   ≟ Map qs with ps ≟ᵐ qs
... | yes refl = yes refl
... | no  ps≢qs = no λ { refl → ps≢qs refl }
List ds  ≟ List es with ds ≟ˡ es
... | yes refl = yes refl
... | no  ds≢es = no λ { refl → ds≢es refl }
I i      ≟ I j with i ℤ.≟ j
... | yes refl = yes refl
... | no  i≢j  = no λ { refl → i≢j refl }
B b      ≟ B c with b BS.≟ c
... | yes refl = yes refl
... | no  b≢c  = no λ { refl → b≢c refl }
Constr _ _ ≟ Map _      = no λ ()
Constr _ _ ≟ List _     = no λ ()
Constr _ _ ≟ I _        = no λ ()
Constr _ _ ≟ B _        = no λ ()
Map _      ≟ Constr _ _ = no λ ()
Map _      ≟ List _     = no λ ()
Map _      ≟ I _        = no λ ()
Map _      ≟ B _        = no λ ()
List _     ≟ Constr _ _ = no λ ()
List _     ≟ Map _      = no λ ()
List _     ≟ I _        = no λ ()
List _     ≟ B _        = no λ ()
I _        ≟ Constr _ _ = no λ ()
I _        ≟ Map _      = no λ ()
I _        ≟ List _     = no λ ()
I _        ≟ B _        = no λ ()
B _        ≟ Constr _ _ = no λ ()
B _        ≟ Map _      = no λ ()
B _        ≟ List _     = no λ ()
B _        ≟ I _        = no λ ()

[]       ≟ˡ []       = yes refl
[]       ≟ˡ (_ ∷ _)  = no λ ()
(_ ∷ _)  ≟ˡ []       = no λ ()
(d ∷ ds) ≟ˡ (e ∷ es) with d ≟ e | ds ≟ˡ es
... | yes refl | yes refl = yes refl
... | no  d≢e  | _        = no λ { refl → d≢e refl }
... | yes _    | no  ds≢es = no λ { refl → ds≢es refl }

[]              ≟ᵐ []              = yes refl
[]              ≟ᵐ (_ ∷ _)         = no λ ()
(_ ∷ _)         ≟ᵐ []              = no λ ()
((d₁ , d₂) ∷ ps) ≟ᵐ ((e₁ , e₂) ∷ qs) with d₁ ≟ e₁ | d₂ ≟ e₂ | ps ≟ᵐ qs
... | yes refl  | yes refl  | yes refl  = yes refl
... | no  d₁≢e₁ | _         | _         = no λ { refl → d₁≢e₁ refl }
... | yes _     | no  d₂≢e₂ | _         = no λ { refl → d₂≢e₂ refl }
... | yes _     | yes _     | no  ps≢qs = no λ { refl → ps≢qs refl }
```

## Builtins

`chooseData d c m l i b` chooses one of its last five arguments according to the
constructor of `d`.

```
chooseData : ∀ {A : Set} → Data → A → A → A → A → A → A
chooseData (Constr _ _) c _ _ _ _ = c
chooseData (Map _)      _ m _ _ _ = m
chooseData (List _)     _ _ l _ _ = l
chooseData (I _)        _ _ _ i _ = i
chooseData (B _)        _ _ _ _ b = b
```

The builtins that build `Data` are its constructors.

```
constrData : ℤ → L.List Data → Data
constrData = Constr

mapData : L.List (Data × Data) → Data
mapData = Map

listData : L.List Data → Data
listData = List

iData : ℤ → Data
iData = I

bData : ByteString → Data
bData = B
```

The builtins that inspect `Data` give the arguments of a constructor, and fail on the
other constructors.

```
unConstrData : Data → Maybe (ℤ × L.List Data)
unConstrData (Constr i ds) = just (i , ds)
unConstrData _             = nothing

unMapData : Data → Maybe (L.List (Data × Data))
unMapData (Map ps) = just ps
unMapData _        = nothing

unListData : Data → Maybe (L.List Data)
unListData (List ds) = just ds
unListData _         = nothing

unIData : Data → Maybe ℤ
unIData (I i) = just i
unIData _     = nothing

unBData : Data → Maybe ByteString
unBData (B b) = just b
unBData _     = nothing
```

`equalsData` decides equality, and the remaining builtins build pairs and empty lists of
`Data`.

```
equalsData : Data → Data → Bool
equalsData d e = isYes (d ≟ e)

mkPairData : Data → Data → Data × Data
mkPairData = _,_

mkNilData : ⊤ → L.List Data
mkNilData _ = []

mkNilPairData : ⊤ → L.List (Data × Data)
mkNilPairData _ = []
```

## Tests

```
private
  b₀ b₁ : ByteString
  b₀ = BS.[]
  b₁ = natToByte 1 (s≤s (s≤s z≤n)) BS.∷ BS.[]

  d : Data
  d = Constr (+ 1) (I (- (+ 2)) ∷ Map ((B b₁ , List []) ∷ []) ∷ [])

  -- `chooseData` picks the argument for the constructor.
  _ : chooseData d 0 1 2 3 4 ≡ 0
  _ = refl

  _ : chooseData (B b₀) 0 1 2 3 4 ≡ 4
  _ = refl

  -- Inspecting gives the arguments of the right constructor, and fails otherwise.
  _ : unConstrData d ≡ just (+ 1 , I (- (+ 2)) ∷ Map ((B b₁ , List []) ∷ []) ∷ [])
  _ = refl

  _ : unIData d ≡ nothing
  _ = refl

  _ : unBData (B b₁) ≡ just b₁
  _ = refl

  -- Equality compares the whole tree, including bytestrings.
  _ : equalsData d d ≡ true
  _ = refl

  _ : equalsData (B b₀) (B b₁) ≡ false
  _ = refl

  _ : equalsData d (Constr (+ 1) (I (- (+ 2)) ∷ Map ((B b₀ , List []) ∷ []) ∷ []))
      ≡ false
  _ = refl

  -- Map entries are compared in order, and repeated keys are kept.
  _ : equalsData (Map ((I (+ 0) , B b₀) ∷ (I (+ 1) , B b₀) ∷ []))
                 (Map ((I (+ 1) , B b₀) ∷ (I (+ 0) , B b₀) ∷ []))
      ≡ false
  _ = refl

  _ : equalsData (Map ((I (+ 0) , B b₀) ∷ []))
                 (Map ((I (+ 0) , B b₀) ∷ (I (+ 0) , B b₀) ∷ []))
      ≡ false
  _ = refl
```
