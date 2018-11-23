\begin{code}
open import Builtin.Constant.Type
open import Data.Nat

module Builtin.Signature
  (Ctx⋆ Kind : Set)
  (∅ : Ctx⋆)
  (_,⋆_ : Ctx⋆ → Kind → Ctx⋆)
  (* # : Kind)
  (_∋⋆_ : Ctx⋆ → Kind → Set)
  (Z : ∀ {Φ J} → (Φ ,⋆ J) ∋⋆ J)
  (S : ∀ {Φ J K} → Φ ∋⋆ J → (Φ ,⋆ K) ∋⋆ J)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (` : ∀ {Φ J} → Φ ∋⋆ J → Φ ⊢⋆ J)
  (con : ∀{φ} → TyCon → φ ⊢⋆ # → φ ⊢⋆ *)
  (boolean : ∀{Γ} → Γ ⊢⋆ *)
  (size⋆ : ∀{φ} → ℕ → φ ⊢⋆ #)
  where
\end{code}

## Imports

\begin{code}

open import Data.List
open import Data.Product renaming (_,_ to _,,_)
\end{code}

\begin{code}

Sig : Ctx⋆ → Set
Sig Δ = List (Δ ⊢⋆ *) × Δ ⊢⋆ *

data Builtin : Set where
  addInteger               : Builtin
  subtractInteger          : Builtin
  multiplyInteger          : Builtin
  divideInteger            : Builtin
  quotientInteger          : Builtin
  remainderInteger         : Builtin
  modInteger               : Builtin
  lessThanInteger          : Builtin
  lessThanEqualsInteger    : Builtin
  greaterThanInteger       : Builtin
  greaterThanEqualsInteger : Builtin
  equalsInteger            : Builtin
  resizeInteger            : Builtin
  sizeOfInteger            : Builtin
  intToByteString          : Builtin

  concatenate      : Builtin
  takeByteString   : Builtin
  dropByteString   : Builtin
  sha2-256         : Builtin
  sha3-256         : Builtin
  verifySignature  : Builtin
  resizeByteString : Builtin
  equalsByteString : Builtin
  txh              : Builtin
  blocknum         : Builtin
  
SIG : Builtin → Σ Ctx⋆ λ Δ → Sig Δ
-- could have just one context so Signatures extend from ∅...
-- going in the other direction could take a substitution as an arg and
-- extend it appropriately...
SIG addInteger =
  (∅ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG subtractInteger = 
  (∅ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG multiplyInteger = 
  (∅ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG divideInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG quotientInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG remainderInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG modInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG lessThanInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG lessThanEqualsInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG greaterThanInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG greaterThanEqualsInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG equalsInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG resizeInteger =
  ((∅ ,⋆ #) ,⋆ #)
  ,,
  (con size (` Z) ∷ con integer (` (S Z)) ∷ [])
  ,,
  con integer (` Z)
SIG sizeOfInteger =
  (∅ ,⋆ #)
  ,,
  con integer (` Z) ∷ []
  ,,
  con size (` Z)
SIG intToByteString =
  (∅ ,⋆ #) ,⋆ #
  ,,
  con size (` Z) ∷ con integer (` (S Z)) ∷ []
  ,,
  con bytestring (` Z)
SIG concatenate =
  ∅ ,⋆ #
  ,,
  con bytestring (` Z) ∷ con bytestring (` Z) ∷ []
  ,,
  con bytestring (` Z)
SIG takeByteString =
  (∅ ,⋆ #)  ,⋆ #
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG dropByteString =
  (∅ ,⋆ #)  ,⋆ #
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG sha2-256 =
  ∅ ,⋆ #
  ,,
  con bytestring (` Z) ∷ []
  ,,
  con bytestring (size⋆ 32)
SIG sha3-256 =
  ∅ ,⋆ #
  ,,
  con bytestring (` Z) ∷ []
  ,,
  con bytestring (size⋆ 32)
SIG verifySignature =
  ((∅ ,⋆ #) ,⋆ #) ,⋆ #
  ,,
  con bytestring (` (S (S Z)))
    ∷ con bytestring (` (S Z))
    ∷ con bytestring (` Z)
    ∷ []
  ,,
  boolean
SIG resizeByteString =
  (∅ ,⋆ #) ,⋆ #
  ,,
  con size (` Z) ∷ con bytestring (` (S Z)) ∷ []
  ,,
  con bytestring (` Z)
SIG equalsByteString =
  ∅ ,⋆ #
  ,,
  con bytestring (` Z) ∷ con bytestring (` Z) ∷ []
  ,,
  boolean
SIG txh = ∅ ,, [] ,, con bytestring (size⋆ 32)
SIG blocknum =
  ∅ ,⋆ #
  ,,
  con size (` Z) ∷ []
  ,,
  con integer (` Z)
\end{code}
