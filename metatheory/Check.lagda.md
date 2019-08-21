```
module Check where
```

```
open import Scoped
open import Type
open import Scoped.Erasure
open import Utils
open import Data.Nat
open import Data.Fin
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

lookup : ∀ Φ → Fin (len⋆ Φ) → Kind
lookup (Φ ,⋆ K) zero    = K
lookup (Φ ,⋆ _) (suc i) = lookup Φ i

lookup' : ∀ Φ (i : Fin (len⋆ Φ)) → Φ ∋⋆ lookup Φ i
lookup' (Φ ,⋆ K) zero    = Z
lookup' (Φ ,⋆ K) (suc i) = S (lookup' Φ i)

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing

return : {A : Set} → A → Maybe A
return = just

open import Data.Bool
eqKind : Kind → Kind → Bool
eqKind * *       = Bool.true
eqKind * (_ ⇒ _) = Bool.false
eqKind (_ ⇒ _) * = Bool.false
eqKind (K ⇒ J) (K' ⇒ J') = eqKind K K' ∧ eqKind J J'

open import Relation.Nullary
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality
eqKind' : Decidable {A = Kind} _≡_
eqKind' * *       = yes refl
eqKind' * (_ ⇒ _) = no λ()
eqKind' (_ ⇒ _) * = no λ()
eqKind' (K ⇒ J) (K' ⇒ J') with eqKind' K K'
... | no  q = no (λ{refl → q refl})
... | yes p with eqKind' J J'
... | yes p' = yes (cong₂ _⇒_ p p')
... | no  q' = no (λ{refl → q' refl})

meqKind : (K K' : Kind) → Maybe (K ≡ K')
meqKind * *       = just refl 
meqKind * (_ ⇒ _) = nothing
meqKind (_ ⇒ _) * = nothing
meqKind (K ⇒ J) (K' ⇒ J') with meqKind K K'
... | nothing = nothing
... | just p with meqKind J J'
... | nothing = nothing
... | just q = just (cong₂ _⇒_ p q)

-- it doesn't seem to be possible to seperate inferring the kind and
-- and producing a typed term, so `inferKind` is here only as a warmup

inferKind : (Φ : Ctx⋆) → ScopedTy (len⋆ Φ) → Maybe Kind
inferKind Φ (` α)       = return (lookup Φ α)
inferKind Φ (A ⇒ B)     = do
  * ← inferKind Φ A
    where _ → nothing
  * ← inferKind Φ B
    where _ → nothing
  return *
inferKind Φ (Π x K A)   = do
  * ← inferKind (Φ ,⋆ K) A
    where _ → nothing
  return * 
inferKind Φ (ƛ x K A)   = do
  J ← inferKind (Φ ,⋆ K) A
  return (K ⇒  J)
inferKind Φ (A · B)     = do
  K ⇒ J ← inferKind Φ A
    where _ → nothing
  K' ← inferKind Φ B
  if eqKind K K' then return J else nothing
inferKind Φ (con _)     = return *
inferKind Φ (μ pat arg) = do 
  (K ⇒ *) ⇒ K' ⇒ * ← inferKind Φ pat
    where _ → nothing
  K'' ← inferKind Φ arg
  if eqKind K K' ∧ eqKind K' K'' then return * else nothing

open import Data.Product
bondKind : (Φ : Ctx⋆)(A : ScopedTy (len⋆ Φ)) → Maybe (Σ Kind (Φ ⊢⋆_))
bondKind Φ (` α)   = return (lookup Φ α , ` (lookup' Φ α))
bondKind Φ (A ⇒ B) = do
  * , A ← bondKind Φ A
    where _ → nothing
  * , B ← bondKind Φ B
    where _ → nothing
  return (* , A ⇒ B)
bondKind Φ (Π x K A) = do
  * , A ← bondKind (Φ ,⋆ K) A
    where _ → nothing
  return (* , Π x A)
bondKind Φ (ƛ x K A) = do
  J , A ← bondKind (Φ ,⋆ K) A
  return (K ⇒ J , ƛ x A)
bondKind Φ (A · B) = do
  K ⇒ J , A ← bondKind Φ A
    where _ → nothing
  K' , B ← bondKind Φ B
  refl ← meqKind K K'
  return (J , A · B)
bondKind Φ (con tc)     = just (* , con tc)
bondKind Φ (μ pat arg) = do
  (K ⇒ *) ⇒ K' ⇒ * , pat ← bondKind Φ pat
    where _ → nothing
  K'' , arg ← bondKind Φ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  return (* , (μ1 · pat · arg))
```
