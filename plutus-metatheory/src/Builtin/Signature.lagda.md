---
title: Builtin Operations Signatures
layout: page
---

This module gives a parameterised implementation of signatures of
builtin operations. It was used in an earlier version of builtins. It
is not used at the moment. Using it for interleaved builtins would
require even more parameters. It is not yet clear if this would be a
win.

```
open import Builtin.Constant.Type
open import Data.Nat

module Builtin.Signature
  (Ctx⋆ Kind : Set)
  (∅ : Ctx⋆)
  (_,⋆_ : Ctx⋆ → Kind → Ctx⋆)
  (* : Kind)
  (_∋⋆_ : Ctx⋆ → Kind → Set)
  (Z : ∀ {Φ J} → (Φ ,⋆ J) ∋⋆ J)
  (S : ∀ {Φ J K} → Φ ∋⋆ J → (Φ ,⋆ K) ∋⋆ J)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (` : ∀ {Φ J} → Φ ∋⋆ J → Φ ⊢⋆ J)
  (con : ∀{φ} → TyCon → φ ⊢⋆ *)
  where
```

## Imports

```

open import Data.List
open import Data.Product renaming (_,_ to _,,_)

open import Builtin
```

```

Sig : Ctx⋆ → Set
Sig Δ = List (Δ ⊢⋆ *) × Δ ⊢⋆ *

SIG : Builtin → Σ Ctx⋆ λ Δ → Sig Δ
-- could have just one context so Signatures extend from ∅...
-- going in the other direction could take a substitution as an arg and
-- extend it appropriately...

-- note the list of arg types is in reverse order...
SIG addInteger =
  ∅ ,, (con integer ∷ con integer ∷ []) ,, con integer
SIG subtractInteger =
  ∅ ,, (con integer ∷ con integer ∷ []) ,, con integer
SIG multiplyInteger =
  ∅ ,, (con integer ∷ con integer ∷ []) ,, con integer
SIG divideInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con integer
SIG quotientInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con integer
SIG remainderInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con integer
SIG modInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con integer
SIG lessThanInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con bool
SIG lessThanEqualsInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con bool
SIG greaterThanInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con bool
SIG greaterThanEqualsInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  con bool
SIG equalsInteger =
  ∅
  ,,
  con integer ∷ con integer  ∷ []
  ,,
  con bool
SIG concatenate =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ []
  ,,
  con bytestring
SIG takeByteString =
  ∅
  ,,
  con integer ∷ con bytestring ∷ []
  ,,
  con bytestring
SIG dropByteString =
  ∅
  ,,
  con integer ∷ con bytestring ∷ []
  ,,
  con bytestring
SIG lessThanByteString =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ []
  ,,
  con bool
SIG greaterThanByteString =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ []
  ,,
  con bool
SIG sha2-256 =
  ∅
  ,,
  con bytestring ∷ []
  ,,
  con bytestring
SIG sha3-256 =
  ∅
  ,,
  con bytestring ∷ []
  ,,
  con bytestring
SIG verifySignature =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ con bytestring ∷ []
  ,,
  con bool
SIG equalsByteString =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ []
  ,,
  con bool
SIG ifThenElse =
  (∅ ,⋆ *)
  ,,
  ` Z ∷ ` Z ∷ con bool ∷ []
  ,,
  ` Z
SIG charToString =
  ∅
  ,,
  con char ∷ []
  ,,
  con string
SIG append =
  ∅
  ,,
  con string ∷ con string ∷ []
  ,,
  con string
SIG trace =
  ∅
  ,,
  con string ∷ []
  ,,
  con unit
```
