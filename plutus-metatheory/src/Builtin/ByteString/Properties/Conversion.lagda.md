---
title: Builtin.ByteString.Properties.Conversion
layout: page
---

This module proves the laws of the conversions between integers and
bytestrings, `integerToByteString` and `byteStringToInteger`, from
[CIP-121](https://cips.cardano.org/cip/CIP-0121). These are the properties
tested by the Haskell test suite `Evaluation.Builtins.Conversion`:

* converting 0 to a bytestring of width `d` gives `d` zero bytes, so its
  length is `d` and every byte is 0;
* converting a positive number at minimal width (width 0) gives a non-empty
  bytestring;
* multiplying by 256 adds a zero byte at the least significant end, and more
  generally `q * 256 + r` converts to the byte `r` next to the conversion of
  `q`, with the least significant byte first (little-endian) or last
  (big-endian);
* `byteStringToInteger` inverts `integerToByteString` at minimal width, a
  single byte converts to its value, and `integerToByteString` at the length
  of a bytestring inverts `byteStringToInteger`.

The conversion of a natural number produces at most 8192 bytes, so the laws
assume the numbers involved are below `256 ^ 8192` (or `256 ^ 8191`, when the
number is multiplied by 256 first).

The proofs go through the little-endian value of a bytestring, `leVal`, which
is defined by structural recursion: the digits computed by `digits256` are the
little-endian representation of the number, and the big-endian conversions are
the little-endian ones reversed.

```
module Builtin.ByteString.Properties.Conversion where
```

## Imports

```
open import Data.Bool using (Bool; true; false; T; _∨_; if_then_else_)
import Data.Bool.Properties as BP
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; z≤n; s≤s)
open import Data.Nat.Base using (_%_; _/_)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕD
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; 0ℤ)
import Data.Integer.Properties as ℤP
open import Data.Maybe using (Maybe; just; nothing; _>>=_; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Builtin.ByteString.Byte
open import Builtin.ByteString.Base
open import Builtin.ByteString.Denotation
open import Builtin.ByteString.Properties.Byte
open import Builtin.ByteString.Properties.Base
open import Builtin.ByteString.Properties.Logical using (index-replicate)
```

## Arithmetic

```
private

  T⇒≡true : ∀ {b} → T b → b ≡ true
  T⇒≡true {true} _ = refl

  -- Appending a base-256 digit below a number below M stays below 256 M.
  digit+256* : ∀ a v M → a < 256 → v < M → a + 256 * v < 256 * M
  digit+256* a v M a< v<M =
    ℕP.<-≤-trans (ℕP.+-monoˡ-< (256 * v) a<)
      (ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.*-suc 256 v))) (ℕP.*-monoʳ-≤ 256 v<M))

  -- A number is its remainder plus 256 times its quotient.
  %+256*/ : ∀ k → k % 256 + 256 * (k / 256) ≡ k
  %+256*/ k = trans (cong (ℕ._+_ (k % 256)) (ℕP.*-comm 256 (k / 256))) (sym (ℕD.m≡m%n+[m/n]*n k 256))

  -- Base-256 digits are unique.
  digit-unique : ∀ a b c d → a < 256 → c < 256 → a + 256 * b ≡ c + 256 * d → a ≡ c × b ≡ d
  digit-unique a b c d a< c< eq = a≡c , b≡d
    where
      rem : ∀ x y → x < 256 → (x + 256 * y) % 256 ≡ x
      rem x y x< = trans (cong (λ z → (x + z) % 256) (ℕP.*-comm 256 y))
                   (trans (ℕD.[m+kn]%n≡m%n x y 256) (ℕD.m<n⇒m%n≡m x<))
      a≡c : a ≡ c
      a≡c = trans (sym (rem a b a<)) (trans (cong (_% 256) eq) (rem c d c<))
      b≡d : b ≡ d
      b≡d = ℕP.*-cancelˡ-≡ b d 256 (ℕP.+-cancelˡ-≡ a _ _ (trans eq (cong (_+ 256 * d) (sym a≡c))))

  *256-pos : ∀ p → 0 < p → 0 < p * 256
  *256-pos (suc p) _ = s≤s z≤n

  /256< : ∀ k M → k < 256 * M → k / 256 < M
  /256< k M k< = ℕD.m<n*o⇒m/o<n (subst (k <_) (ℕP.*-comm 256 M) k<)
```

## Little-endian values

The value of a bytestring read with the least significant byte first.

```
leVal : ByteString → ℕ
leVal [] = 0
leVal (x ∷ xs) = byteToℕ x + 256 * leVal xs

leVal< : ∀ xs → leVal xs < 256 ^ lengthℕ xs
leVal< [] = s≤s z≤n
leVal< (x ∷ xs) = digit+256* (byteToℕ x) (leVal xs) _ (byteToℕ<256 x) (leVal< xs)

leVal-zeros : ∀ n → leVal (replicateBS n 0B) ≡ 0
leVal-zeros zero = refl
leVal-zeros (suc n) = cong (256 *_) (leVal-zeros n)

leVal-++-zeros : ∀ xs n → leVal (xs ++ᵇ replicateBS n 0B) ≡ leVal xs
leVal-++-zeros [] n = leVal-zeros n
leVal-++-zeros (x ∷ xs) n = cong (λ v → byteToℕ x + 256 * v) (leVal-++-zeros xs n)
```

Two bytestrings of the same length with the same value are equal.

```
leVal-injective : ∀ xs ys → lengthℕ xs ≡ lengthℕ ys → leVal xs ≡ leVal ys → xs ≡ ys
leVal-injective [] [] _ _ = refl
leVal-injective (x ∷ xs) (y ∷ ys) len eq =
  cong₂ _∷_ (byteToℕ-injective {x} {y} (proj₁ digits))
            (leVal-injective xs ys (ℕP.suc-injective len) (proj₂ digits))
  where
    digits : byteToℕ x ≡ byteToℕ y × leVal xs ≡ leVal ys
    digits = digit-unique (byteToℕ x) (leVal xs) (byteToℕ y) (leVal ys) (byteToℕ<256 x) (byteToℕ<256 y) eq
```

## Reversal and big-endian values

```
reverseAcc-++ᵇ : ∀ acc xs → reverseAcc acc xs ≡ reverseBS xs ++ᵇ acc
reverseAcc-++ᵇ acc [] = refl
reverseAcc-++ᵇ acc (x ∷ xs) = begin
  reverseAcc (x ∷ acc) xs
  ≡⟨ reverseAcc-++ᵇ (x ∷ acc) xs ⟩
  reverseBS xs ++ᵇ (x ∷ acc)
  ≡⟨ ++ᵇ-assoc (reverseBS xs) (x ∷ []) acc ⟨
  (reverseBS xs ++ᵇ (x ∷ [])) ++ᵇ acc
  ≡⟨ cong (_++ᵇ acc) (reverseAcc-++ᵇ (x ∷ []) xs) ⟨
  reverseBS (x ∷ xs) ++ᵇ acc
  ∎
  where
    ++ᵇ-assoc : ∀ xs ys zs → (xs ++ᵇ ys) ++ᵇ zs ≡ xs ++ᵇ (ys ++ᵇ zs)
    ++ᵇ-assoc [] ys zs = refl
    ++ᵇ-assoc (x ∷ xs) ys zs = cong (x ∷_) (++ᵇ-assoc xs ys zs)

reverseBS-∷ : ∀ x xs → reverseBS (x ∷ xs) ≡ reverseBS xs ++ᵇ (x ∷ [])
reverseBS-∷ x xs = reverseAcc-++ᵇ (x ∷ []) xs

private

  ++ᵇ-assoc : ∀ xs ys zs → (xs ++ᵇ ys) ++ᵇ zs ≡ xs ++ᵇ (ys ++ᵇ zs)
  ++ᵇ-assoc [] ys zs = refl
  ++ᵇ-assoc (x ∷ xs) ys zs = cong (x ∷_) (++ᵇ-assoc xs ys zs)

reverseBS-++ᵇ : ∀ xs ys → reverseBS (xs ++ᵇ ys) ≡ reverseBS ys ++ᵇ reverseBS xs
reverseBS-++ᵇ [] ys = sym (++ᵇ-identityʳ (reverseBS ys))
reverseBS-++ᵇ (x ∷ xs) ys = begin
  reverseBS (x ∷ (xs ++ᵇ ys))
  ≡⟨ reverseBS-∷ x (xs ++ᵇ ys) ⟩
  reverseBS (xs ++ᵇ ys) ++ᵇ (x ∷ [])
  ≡⟨ cong (_++ᵇ (x ∷ [])) (reverseBS-++ᵇ xs ys) ⟩
  (reverseBS ys ++ᵇ reverseBS xs) ++ᵇ (x ∷ [])
  ≡⟨ ++ᵇ-assoc (reverseBS ys) (reverseBS xs) (x ∷ []) ⟩
  reverseBS ys ++ᵇ (reverseBS xs ++ᵇ (x ∷ []))
  ≡⟨ cong (reverseBS ys ++ᵇ_) (reverseBS-∷ x xs) ⟨
  reverseBS ys ++ᵇ reverseBS (x ∷ xs)
  ∎

reverseBS-involutive : ∀ xs → reverseBS (reverseBS xs) ≡ xs
reverseBS-involutive [] = refl
reverseBS-involutive (x ∷ xs) = begin
  reverseBS (reverseBS (x ∷ xs))
  ≡⟨ cong reverseBS (reverseBS-∷ x xs) ⟩
  reverseBS (reverseBS xs ++ᵇ (x ∷ []))
  ≡⟨ reverseBS-++ᵇ (reverseBS xs) (x ∷ []) ⟩
  x ∷ reverseBS (reverseBS xs)
  ≡⟨ cong (x ∷_) (reverseBS-involutive xs) ⟩
  x ∷ xs
  ∎

lengthℕ-reverseBS : ∀ xs → lengthℕ (reverseBS xs) ≡ lengthℕ xs
lengthℕ-reverseBS [] = refl
lengthℕ-reverseBS (x ∷ xs) = begin
  lengthℕ (reverseBS (x ∷ xs))
  ≡⟨ cong lengthℕ (reverseBS-∷ x xs) ⟩
  lengthℕ (reverseBS xs ++ᵇ (x ∷ []))
  ≡⟨ lengthℕ-++ᵇ (reverseBS xs) (x ∷ []) ⟩
  lengthℕ (reverseBS xs) + 1
  ≡⟨ cong (_+ 1) (lengthℕ-reverseBS xs) ⟩
  lengthℕ xs + 1
  ≡⟨ ℕP.+-comm (lengthℕ xs) 1 ⟩
  suc (lengthℕ xs)
  ∎

reverseBS-zeros : ∀ n → reverseBS (replicateBS n 0B) ≡ replicateBS n 0B
reverseBS-zeros zero = refl
reverseBS-zeros (suc n) = begin
  reverseBS (0B ∷ replicateBS n 0B)
  ≡⟨ reverseBS-∷ 0B (replicateBS n 0B) ⟩
  reverseBS (replicateBS n 0B) ++ᵇ (0B ∷ [])
  ≡⟨ cong (_++ᵇ (0B ∷ [])) (reverseBS-zeros n) ⟩
  replicateBS n 0B ++ᵇ replicateBS 1 0B
  ≡⟨ replicateBS-+ n 1 0B ⟩
  replicateBS (n + 1) 0B
  ≡⟨ cong (λ m → replicateBS m 0B) (ℕP.+-comm n 1) ⟩
  replicateBS (suc n) 0B
  ∎
```

`byteStringToℕ` reads the most significant byte first, so it is the
little-endian value of the reversed bytestring.

```
private

  byteStringToℕAcc-++ᵇ
    : ∀ acc xs ys → byteStringToℕAcc acc (xs ++ᵇ ys) ≡ byteStringToℕAcc (byteStringToℕAcc acc xs) ys
  byteStringToℕAcc-++ᵇ acc [] ys = refl
  byteStringToℕAcc-++ᵇ acc (x ∷ xs) ys = byteStringToℕAcc-++ᵇ (acc * 256 + byteToℕ x) xs ys

byteStringToℕ-reverseBS : ∀ xs → byteStringToℕ (reverseBS xs) ≡ leVal xs
byteStringToℕ-reverseBS [] = refl
byteStringToℕ-reverseBS (x ∷ xs) = begin
  byteStringToℕ (reverseBS (x ∷ xs))
  ≡⟨ cong byteStringToℕ (reverseBS-∷ x xs) ⟩
  byteStringToℕ (reverseBS xs ++ᵇ (x ∷ []))
  ≡⟨ byteStringToℕAcc-++ᵇ 0 (reverseBS xs) (x ∷ []) ⟩
  byteStringToℕ (reverseBS xs) * 256 + byteToℕ x
  ≡⟨ cong (λ v → v * 256 + byteToℕ x) (byteStringToℕ-reverseBS xs) ⟩
  leVal xs * 256 + byteToℕ x
  ≡⟨ ℕP.+-comm (leVal xs * 256) (byteToℕ x) ⟩
  byteToℕ x + leVal xs * 256
  ≡⟨ cong (ℕ._+_ (byteToℕ x)) (ℕP.*-comm (leVal xs) 256) ⟩
  leVal (x ∷ xs)
  ∎

BStoI-false : ∀ bs → BStoI false bs ≡ + leVal bs
BStoI-false bs = cong +_ (byteStringToℕ-reverseBS bs)

BStoI-true : ∀ bs → BStoI true bs ≡ + leVal (reverseBS bs)
BStoI-true bs =
  cong +_ (trans (cong byteStringToℕ (sym (reverseBS-involutive bs))) (byteStringToℕ-reverseBS (reverseBS bs)))
```

## The digits of a number

`digits256 f k` computes the little-endian base-256 digits of `k`, or fails if
there are more than `f` of them. It succeeds on numbers below `256 ^ f`, it
does not depend on the bound once it succeeds, its digits have the value `k`,
and there are no more of them than needed.

```
-- Opaque: callers only use the digits through the equation, and unfolding
-- the proof of the bound (which mentions `256 ^ f`) is expensive.
opaque
  digits256-just : ∀ f k → k < 256 ^ f → Σ ByteString λ ds → digits256 f k ≡ just ds
  digits256-just f zero _ = [] , refl
  digits256-just zero (suc k) (s≤s ())
  digits256-just (suc f) (suc k) k< =
    let (ds , eq) = digits256-just f (suc k / 256) (/256< (suc k) (256 ^ f) k<)
    in ℕToByte (suc k % 256) ∷ ds , cong (map (ℕToByte (suc k % 256) ∷_)) eq

-- The digits of a positive number: its remainder, then the digits of its quotient.
digits256-inv
  : ∀ f k ds → digits256 (suc f) (suc k) ≡ just ds
  → Σ ByteString λ ds′ → (digits256 f (suc k / 256) ≡ just ds′) × (ds ≡ ℕToByte (suc k % 256) ∷ ds′)
digits256-inv f k ds eq with digits256 f (suc k / 256) in eq′
digits256-inv f k .(ℕToByte (suc k % 256) ∷ ds′) refl | just ds′ = ds′ , refl , refl

digits256-suc : ∀ f k ds → digits256 f k ≡ just ds → digits256 (suc f) k ≡ just ds
digits256-suc f zero .[] refl = refl
digits256-suc (suc f) (suc k) ds eq =
  let (ds′ , eq′ , ds≡) = digits256-inv f k ds eq
  in trans (cong (map (ℕToByte (suc k % 256) ∷_)) (digits256-suc f (suc k / 256) ds′ eq′))
           (cong just (sym ds≡))

digits256-leVal : ∀ f k ds → digits256 f k ≡ just ds → leVal ds ≡ k
digits256-leVal f zero .[] refl = refl
digits256-leVal (suc f) (suc k) ds eq =
  let (ds′ , eq′ , ds≡) = digits256-inv f k ds eq
  in begin
    leVal ds
    ≡⟨ cong leVal ds≡ ⟩
    byteToℕ (ℕToByte (suc k % 256)) + 256 * leVal ds′
    ≡⟨ cong₂ (λ a v → a + 256 * v) (byteToℕ-ℕToByte (suc k % 256) (ℕD.m%n<n (suc k) 256))
                                    (digits256-leVal f (suc k / 256) ds′ eq′) ⟩
    suc k % 256 + 256 * (suc k / 256)
    ≡⟨ %+256*/ (suc k) ⟩
    suc k
    ∎

digits256-length : ∀ f k ds m → digits256 f k ≡ just ds → k < 256 ^ m → lengthℕ ds ≤ m
digits256-length f zero .[] m refl _ = z≤n
digits256-length (suc f) (suc k) ds zero eq (s≤s ())
digits256-length (suc f) (suc k) ds (suc m) eq k< =
  let (ds′ , eq′ , ds≡) = digits256-inv f k ds eq
  in subst (λ d → lengthℕ d ≤ suc m) (sym ds≡)
       (s≤s (digits256-length f (suc k / 256) ds′ m eq′ (/256< (suc k) (256 ^ m) k<)))
```

## integerToByteString

For a valid width and a non-negative number, `integerToByteString` is the
conversion of natural numbers.

```
ItoBS-ℕ : ∀ e w k → w ≤ 8192 → ItoBS e (+ w) (+ k) ≡ ℕToByteString e w k
ItoBS-ℕ e w k w≤ rewrite T⇒≡true (ℕP.≤⇒≤ᵇ w≤) = refl
```

The conversion of a positive number, given its digits.

```
ℕToByteString-digits
  : ∀ e w n ds → digits256 8192 (suc n) ≡ just ds
  → ℕToByteString e w (suc n)
    ≡ (if (w ℕ.≡ᵇ 0) ∨ (lengthℕ ds ℕ.≤ᵇ w)
       then just (if e then replicateBS (w ∸ lengthℕ ds) 0B ++ᵇ reverseBS ds
                       else ds ++ᵇ replicateBS (w ∸ lengthℕ ds) 0B)
       else nothing)
ℕToByteString-digits e w n ds eq rewrite eq = refl
```

The big-endian conversion is the little-endian one reversed.

```
ℕToByteString-true : ∀ w k → ℕToByteString true w k ≡ map reverseBS (ℕToByteString false w k)
ℕToByteString-true w zero = cong just (sym (reverseBS-zeros w))
ℕToByteString-true w (suc n) with digits256 8192 (suc n)
... | nothing = refl
... | just ds with (w ℕ.≡ᵇ 0) ∨ (lengthℕ ds ℕ.≤ᵇ w)
...   | false = refl
...   | true = cong just (sym (begin
  reverseBS (ds ++ᵇ replicateBS (w ∸ lengthℕ ds) 0B)
  ≡⟨ reverseBS-++ᵇ ds _ ⟩
  reverseBS (replicateBS (w ∸ lengthℕ ds) 0B) ++ᵇ reverseBS ds
  ≡⟨ cong (_++ᵇ reverseBS ds) (reverseBS-zeros (w ∸ lengthℕ ds)) ⟩
  replicateBS (w ∸ lengthℕ ds) 0B ++ᵇ reverseBS ds
  ∎))
```

At minimal width (width 0), the conversion gives exactly the digits, least
significant first (little-endian) or last (big-endian).

```
minimal : Bool → ByteString → ByteString
minimal e ds = if e then reverseBS ds else ds

ItoBS-minimal : ∀ e k ds → digits256 8192 k ≡ just ds → ItoBS e 0ℤ (+ k) ≡ just (minimal e ds)
ItoBS-minimal true zero .[] refl = refl
ItoBS-minimal false zero .[] refl = refl
ItoBS-minimal true (suc n) ds eq rewrite eq =
  cong (λ z → just (replicateBS z 0B ++ᵇ reverseBS ds)) (ℕP.0∸n≡0 (lengthℕ ds))
ItoBS-minimal false (suc n) ds eq rewrite eq =
  cong just (trans (cong (λ z → ds ++ᵇ replicateBS z 0B) (ℕP.0∸n≡0 (lengthℕ ds))) (++ᵇ-identityʳ ds))
```

At a given width, a number that fits is converted to a bytestring of that
width with the right value.

```
ℕToByteString-width
  : ∀ w k → k < 256 ^ w → w ≤ 8192
  → Σ ByteString λ r → (ℕToByteString false w k ≡ just r) × (lengthℕ r ≡ w) × (leVal r ≡ k)
ℕToByteString-width w zero _ _ = replicateBS w 0B , refl , lengthℕ-replicateBS w 0B , leVal-zeros w
ℕToByteString-width w (suc n) k< w≤ =
  r , trans (ℕToByteString-digits false w n ds eq) valid , len , val
  where
    found = digits256-just 8192 (suc n) (ℕP.<-≤-trans k< (ℕP.^-monoʳ-≤ 256 w≤))
    ds = proj₁ found
    eq = proj₂ found
    len≤ : lengthℕ ds ≤ w
    len≤ = digits256-length 8192 (suc n) ds w eq k<
    r = ds ++ᵇ replicateBS (w ∸ lengthℕ ds) 0B
    valid : (if (w ℕ.≡ᵇ 0) ∨ (lengthℕ ds ℕ.≤ᵇ w) then just r else nothing) ≡ just r
    valid rewrite T⇒≡true (ℕP.≤⇒≤ᵇ len≤) | BP.∨-zeroʳ (w ℕ.≡ᵇ 0) = refl
    len : lengthℕ r ≡ w
    len = trans (lengthℕ-++ᵇ ds _) (trans (cong (ℕ._+_ (lengthℕ ds)) (lengthℕ-replicateBS _ 0B))
                                          (ℕP.m+[n∸m]≡n len≤))
    val : leVal r ≡ suc n
    val = trans (leVal-++-zeros ds _) (digits256-leVal 8192 (suc n) ds eq)
```

### Converting zero

Converting 0 at width `d` gives `d` zero bytes: the result has length `d`,
and every byte of it is 0.

```
ItoBS-zero : ∀ e d → d ≤ 8192 → ItoBS e (+ d) 0ℤ ≡ just (replicateBS d 0B)
ItoBS-zero e d d≤ = ItoBS-ℕ e d 0 d≤

ItoBS-zero-length
  : ∀ e d → d ≤ 8192 → (ItoBS e (+ d) 0ℤ >>= λ bs → just (lengthBS bs)) ≡ just (+ d)
ItoBS-zero-length e d d≤ rewrite ItoBS-zero e d d≤ =
  cong just (trans (lengthBS-lengthℕ (replicateBS d 0B)) (cong +_ (lengthℕ-replicateBS d 0B)))

ItoBS-zero-index
  : ∀ e k j → k ≤ 8192 → j < k → (ItoBS e (+ k) 0ℤ >>= λ bs → index bs (+ j)) ≡ just 0ℤ
ItoBS-zero-index e k j k≤ j<k rewrite ItoBS-zero e k k≤ = index-replicate k 0B j j<k
```

### Converting a positive number

At minimal width, a positive number converts to a non-empty bytestring.

```
ItoBS-positive
  : ∀ e p → 0 < p → p < 256 ^ 8192
  → Σ ByteString λ bs → (ItoBS e 0ℤ (+ p) ≡ just bs) × (0 < lengthℕ bs)
ItoBS-positive e (suc n) _ p< = minimal e ds , ItoBS-minimal e (suc n) ds eq , nonempty e
  where
    found = digits256-just 8192 (suc n) p<
    ds = proj₁ found
    eq = proj₂ found
    ds≢[] : 0 < lengthℕ ds
    ds≢[] = let (_ , _ , ds≡) = digits256-inv 8191 n ds eq in subst (λ d → 0 < lengthℕ d) (sym ds≡) (s≤s z≤n)
    nonempty : ∀ e → 0 < lengthℕ (minimal e ds)
    nonempty true = subst (0 <_) (sym (lengthℕ-reverseBS ds)) ds≢[]
    nonempty false = ds≢[]
```

The digits of `q * 256 + r`, for a byte value `r`, are `r` followed by the
digits of `q`. In particular, the digits of `p * 256` are 0 followed by those
of `p`.

```
private

  mod≡ : ∀ q r → r < 256 → (q * 256 + r) % 256 ≡ r
  mod≡ q r r< = trans (cong (_% 256) (ℕP.+-comm (q * 256) r))
                (trans (ℕD.[m+kn]%n≡m%n r q 256) (ℕD.m<n⇒m%n≡m r<))

  div≡ : ∀ q r → r < 256 → (q * 256 + r) / 256 ≡ q
  div≡ q r r< =
    trans (ℕD.+-distrib-/ (q * 256) r
            (subst (_< 256) (sym (cong (_+ r % 256) (ℕD.m*n%n≡0 q 256)))
                   (ℕP.≤-<-trans (ℕD.m%n≤m r 256) r<)))
    (trans (cong₂ _+_ (ℕD.m*n/n≡m q 256) (ℕD.m<n⇒m/n≡0 r<)) (ℕP.+-identityʳ q))

  digits256-unfold
    : ∀ f k → 0 < k → digits256 (suc f) k ≡ map (ℕToByte (k % 256) ∷_) (digits256 f (k / 256))
  digits256-unfold f (suc k) _ = refl

  digits256-step
    : ∀ q r ds → r < 256 → 0 < q * 256 + r → digits256 8191 q ≡ just ds
    → digits256 8192 (q * 256 + r) ≡ just (ℕToByte r ∷ ds)
  digits256-step q r ds r< pos eq =
    trans (digits256-unfold 8191 (q * 256 + r) pos)
    (trans (cong₂ (λ a b → map (ℕToByte a ∷_) (digits256 8191 b)) (mod≡ q r r<) (div≡ q r r<))
           (cong (map (ℕToByte r ∷_)) eq))

  digits256-8191 : ∀ q → q < 256 ^ 8191 → Σ ByteString λ ds → (digits256 8191 q ≡ just ds) × (digits256 8192 q ≡ just ds)
  digits256-8191 q q< =
    let (ds , eq) = digits256-just 8191 q q< in ds , eq , digits256-suc 8191 q ds eq

  digits256-*256
    : ∀ p ds → 0 < p → digits256 8191 p ≡ just ds → digits256 8192 (p * 256) ≡ just (ℕToByte 0 ∷ ds)
  digits256-*256 p ds 0<p eq =
    subst (λ k → digits256 8192 k ≡ just (ℕToByte 0 ∷ ds)) (ℕP.+-identityʳ (p * 256))
      (digits256-step p 0 ds (s≤s z≤n) (subst (0 <_) (sym (ℕP.+-identityʳ (p * 256))) (*256-pos p 0<p)) eq)
```

Multiplying a positive number by 256 adds a zero byte at the least
significant end: at the start for little-endian, at the end for big-endian.

```
ItoBS-*256-false
  : ∀ p → 0 < p → p < 256 ^ 8191
  → ItoBS false 0ℤ (+ (p * 256)) ≡ (ItoBS false 0ℤ (+ p) >>= cons 0ℤ)
ItoBS-*256-false p 0<p p< =
  let (ds , eq₁ , eq₂) = digits256-8191 p p<
  in trans (ItoBS-minimal false (p * 256) (ℕToByte 0 ∷ ds) (digits256-*256 p ds 0<p eq₁))
           (sym (cong (_>>= cons 0ℤ) (ItoBS-minimal false p ds eq₂)))

ItoBS-*256-true
  : ∀ p → 0 < p → p < 256 ^ 8191
  → ItoBS true 0ℤ (+ (p * 256)) ≡ (ItoBS true 0ℤ (+ p) >>= λ bs → just (concat bs (0B ∷ [])))
ItoBS-*256-true p 0<p p< =
  let (ds , eq₁ , eq₂) = digits256-8191 p p<
  in trans (ItoBS-minimal true (p * 256) (ℕToByte 0 ∷ ds) (digits256-*256 p ds 0<p eq₁))
     (trans (cong just (trans (reverseBS-∷ 0B ds) (sym (concat≡++ᵇ (reverseBS ds) (0B ∷ [])))))
            (sym (cong (λ m → m >>= λ bs → just (concat bs (0B ∷ []))) (ItoBS-minimal true p ds eq₂))))
```

More generally, `q * 256 + r` converts to the byte `r` next to the conversion
of `q`, for a non-zero byte value `r` and any `q ≥ 0`.

```
ItoBS-*256+-false
  : ∀ q r → 0 < r → r < 256 → q < 256 ^ 8191
  → ItoBS false 0ℤ (+ (q * 256 + r))
    ≡ (ItoBS false 0ℤ (+ r) >>= λ rs → ItoBS false 0ℤ (+ q) >>= λ qs → just (concat rs qs))
ItoBS-*256+-false q r 0<r r< q< =
  let (ds , eq₁ , eq₂) = digits256-8191 q q<
  in trans (ItoBS-minimal false (q * 256 + r) (ℕToByte r ∷ ds)
              (digits256-step q r ds r< (ℕP.<-≤-trans 0<r (ℕP.m≤n+m r (q * 256))) eq₁))
     (sym (trans (cong (λ m → m >>= λ rs → ItoBS false 0ℤ (+ q) >>= λ qs → just (concat rs qs))
                       (ItoBS-minimal false r (ℕToByte r ∷ []) (digits256-step 0 r [] r< 0<r refl)))
                 (cong (λ m → m >>= λ qs → just (concat (ℕToByte r ∷ []) qs)) (ItoBS-minimal false q ds eq₂))))

ItoBS-*256+-true
  : ∀ q r → 0 < r → r < 256 → q < 256 ^ 8191
  → ItoBS true 0ℤ (+ (q * 256 + r))
    ≡ (ItoBS true 0ℤ (+ q) >>= λ qs → ItoBS true 0ℤ (+ r) >>= λ rs → just (concat qs rs))
ItoBS-*256+-true q r 0<r r< q< =
  let (ds , eq₁ , eq₂) = digits256-8191 q q<
  in trans (ItoBS-minimal true (q * 256 + r) (ℕToByte r ∷ ds)
              (digits256-step q r ds r< (ℕP.<-≤-trans 0<r (ℕP.m≤n+m r (q * 256))) eq₁))
     (trans (cong just (trans (reverseBS-∷ (ℕToByte r) ds) (sym (concat≡++ᵇ (reverseBS ds) (ℕToByte r ∷ [])))))
     (sym (trans (cong (λ m → m >>= λ qs → ItoBS true 0ℤ (+ r) >>= λ rs → just (concat qs rs))
                       (ItoBS-minimal true q ds eq₂))
                 (cong (λ m → m >>= λ rs → just (concat (reverseBS ds) rs))
                       (ItoBS-minimal true r (ℕToByte r ∷ []) (digits256-step 0 r [] r< 0<r refl))))))
```

## byteStringToInteger

`byteStringToInteger` inverts `integerToByteString` at minimal width.

```
BStoI-ItoBS
  : ∀ e q → q < 256 ^ 8192
  → (ItoBS e 0ℤ (+ q) >>= λ bs → just (BStoI e bs)) ≡ just (+ q)
BStoI-ItoBS e q q< =
  trans (cong (λ m → m >>= λ bs → just (BStoI e bs)) (ItoBS-minimal e q ds eq)) (cong just (value e))
  where
    found = digits256-just 8192 q q<
    ds = proj₁ found
    eq = proj₂ found
    value : ∀ e → BStoI e (minimal e ds) ≡ + q
    value true = trans (BStoI-true (reverseBS ds))
                 (cong +_ (trans (cong leVal (reverseBS-involutive ds)) (digits256-leVal 8192 q ds eq)))
    value false = trans (BStoI-false ds) (cong +_ (digits256-leVal 8192 q ds eq))
```

A single byte converts to its value, with either byte order.

```
cons-valid : ∀ w xs → w < 256 → cons (+ w) xs ≡ just (ℕToByte w ∷ xs)
cons-valid w xs w< with + 0 ℤ.≤? + w
... | no 0≰w = contradiction (ℤ.+≤+ z≤n) 0≰w
... | yes _ rewrite T⇒≡true (ℕP.≤⇒≤ᵇ (ℕP.<⇒≤pred w<)) = refl

BStoI-cons
  : ∀ e w → w < 256 → (cons (+ w) [] >>= λ bs → just (BStoI e bs)) ≡ just (+ w)
BStoI-cons e w w< rewrite cons-valid w [] w< = cong just (value e)
  where
    value : ∀ e → BStoI e (ℕToByte w ∷ []) ≡ + w
    value true = cong +_ (byteToℕ-ℕToByte w w<)
    value false = cong +_ (byteToℕ-ℕToByte w w<)
```

`integerToByteString` at the length of a bytestring inverts
`byteStringToInteger`, for bytestrings of at most 8192 bytes.

```
ItoBS-BStoI-false : ∀ bs → lengthℕ bs ≤ 8192 → ItoBS false (lengthBS bs) (BStoI false bs) ≡ just bs
ItoBS-BStoI-false bs len≤ =
  trans (cong₂ (ItoBS false) (lengthBS-lengthℕ bs) (BStoI-false bs))
  (trans (ItoBS-ℕ false (lengthℕ bs) (leVal bs) len≤)
         (go (ℕToByteString-width (lengthℕ bs) (leVal bs) (leVal< bs) len≤)))
  where
    go : (Σ ByteString λ r → (ℕToByteString false (lengthℕ bs) (leVal bs) ≡ just r)
                           × (lengthℕ r ≡ lengthℕ bs) × (leVal r ≡ leVal bs))
       → ℕToByteString false (lengthℕ bs) (leVal bs) ≡ just bs
    go (r , eq , len , val) = trans eq (cong just (leVal-injective r bs len val))

ItoBS-BStoI-true : ∀ bs → lengthℕ bs ≤ 8192 → ItoBS true (lengthBS bs) (BStoI true bs) ≡ just bs
ItoBS-BStoI-true bs len≤ =
  trans (cong₂ (ItoBS true) (lengthBS-lengthℕ bs) (BStoI-true bs))
  (trans (ItoBS-ℕ true (lengthℕ bs) v len≤)
  (trans (ℕToByteString-true (lengthℕ bs) v)
         (go (ℕToByteString-width (lengthℕ bs) v
                (subst (λ n → v < 256 ^ n) (lengthℕ-reverseBS bs) (leVal< (reverseBS bs))) len≤))))
  where
    v = leVal (reverseBS bs)
    go : (Σ ByteString λ r → (ℕToByteString false (lengthℕ bs) v ≡ just r)
                           × (lengthℕ r ≡ lengthℕ bs) × (leVal r ≡ v))
       → map reverseBS (ℕToByteString false (lengthℕ bs) v) ≡ just bs
    go (r , eq , len , val) =
      trans (cong (map reverseBS) eq)
            (cong just (trans (cong reverseBS (leVal-injective r (reverseBS bs)
                                                 (trans len (sym (lengthℕ-reverseBS bs))) val))
                              (reverseBS-involutive bs)))

ItoBS-BStoI : ∀ e bs → lengthℕ bs ≤ 8192 → ItoBS e (lengthBS bs) (BStoI e bs) ≡ just bs
ItoBS-BStoI true = ItoBS-BStoI-true
ItoBS-BStoI false = ItoBS-BStoI-false
```
