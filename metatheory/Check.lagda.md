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


