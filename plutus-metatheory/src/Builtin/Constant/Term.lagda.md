```
open import Builtin.Constant.Type
```

```
module Builtin.Constant.Term
  (Ctx⋆ Kind : Set)
  (* : Kind)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (con : ∀{φ} → TyCon → φ ⊢⋆ *)
  where

open import Builtin

open import Data.Integer
open import Data.String
open import Data.Char
open import Data.Bool
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
  char       :
      (c : Char)
    → TermCon (con char)
  unit       : TermCon (con unit)
```
