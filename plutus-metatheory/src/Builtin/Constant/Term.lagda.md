```
open import Builtin.Constant.Type
open import Utils hiding (TermCon)
```

```
module Builtin.Constant.Term
  (Ctx⋆ Kind : Set)
  (* : Kind)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (con : ∀{Φ} → TyCon Ctx⋆ (_⊢⋆ *) Φ → Φ ⊢⋆ *)
  where
```

## Imports

```
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Utils using (_×_)
```

## Term Constants

```
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    :
      (i : ℤ)
    → TermCon (con (atomic integer))
  bytestring :
      (b : ByteString)
    → TermCon (con (atomic bytestring))
  string     :
      (s : String)
    → TermCon (con (atomic string))
  bool       :
      (b : Bool)
    → TermCon (con (atomic bool))
  unit       : TermCon (con (atomic unit))
  pdata      : DATA → TermCon (con (atomic pdata))  
  pairDATA   : (d₁ : DATA) → (d₂ : DATA) → TermCon (con (pair (con (atomic pdata)) (con (atomic pdata)))) 
  pairID     : (i : ℤ) → (ds : List DATA) → TermCon (con (pair (con (atomic integer)) (con (list (con (atomic pdata))))))
  listData   : (xs : List DATA) → TermCon (con (list (con (atomic pdata))))
  listPair   : (xs : List (DATA × DATA)) → TermCon (con (list (con (pair (con (atomic pdata)) (con (atomic pdata))))))

```
