\begin{code}
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
  (boolean : ∀{Γ} → Γ ⊢⋆ *)
  where
\end{code}

## Imports

\begin{code}

open import Data.List
open import Data.Product renaming (_,_ to _,,_)

open import Builtin
\end{code}

\begin{code}

Sig : Ctx⋆ → Set
Sig Δ = List (Δ ⊢⋆ *) × Δ ⊢⋆ *

SIG : Builtin → Σ Ctx⋆ λ Δ → Sig Δ
-- could have just one context so Signatures extend from ∅...
-- going in the other direction could take a substitution as an arg and
-- extend it appropriately...
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
  boolean
SIG lessThanEqualsInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  boolean
SIG greaterThanInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  boolean
SIG greaterThanEqualsInteger =
  ∅
  ,,
  con integer ∷ con integer ∷ []
  ,,
  boolean
SIG equalsInteger =
  ∅
  ,,
  con integer ∷ con integer  ∷ []
  ,,
  boolean
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
  boolean
SIG equalsByteString =
  ∅
  ,,
  con bytestring ∷ con bytestring ∷ []
  ,,
  boolean
\end{code}
