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
```

## Term Constants

```
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    :
      (i : ℤ)
    → TermCon (con integer)
  bytestring :
      (b : ByteString)
    → TermCon (con bytestring)
  string     :
      (s : String)
    → TermCon (con string)
  bool       :
      (b : Bool)
    → TermCon (con bool)
  unit       : TermCon (con unit)
  pdata       : DATA → TermCon (con pdata)  
```
