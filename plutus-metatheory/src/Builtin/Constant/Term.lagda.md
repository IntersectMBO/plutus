```
open import Builtin.Constant.Type
import Utils as U
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
open import Data.List using (List)
```

## Term Constants

```
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  tmInteger    :
      (i : ℤ)
    → TermCon (con integer)
  tmBytestring :
      (b : U.ByteString)
    → TermCon (con bytestring)
  tmString     :
      (s : String)
    → TermCon (con string)
  tmBool       :
      (b : Bool)
    → TermCon (con bool)
  tmUnit      : TermCon (con unit)
  tmData      : U.DATA → TermCon (con pdata)
  tmBls12-381-g1-element : U.Bls12-381-G1-Element → TermCon (con bls12-381-g1-element)
  tmBls12-381-g2-element : U.Bls12-381-G2-Element → TermCon (con bls12-381-g2-element)
  tmBls12-381-mlresult   : U.Bls12-381-MlResult   → TermCon (con bls12-381-mlresult)
```
 