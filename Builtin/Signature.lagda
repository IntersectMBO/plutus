\begin{code}
module Builtin.Signature where
\end{code}

## Imports

\begin{code}
open import Type
open import Builtin.Constant.Type

open import Data.List
open import Data.Product renaming (_,_ to _,,_)
\end{code}

\begin{code}

Sig : Ctx⋆ → Ctx⋆ → Set
Sig Δ Γ = List (Δ ⊢⋆ *) × Δ ⊢⋆ *

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
  
SIG : Builtin → ∀ Γ → Σ Ctx⋆ λ Δ → Sig Δ Γ
-- could have just one context so Signatures extend from ∅...
-- going in the other direction could take a substitution as an arg and
-- extend it appropriately...
SIG addInteger       Γ =
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG subtractInteger Γ = 
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG multiplyInteger Γ = 
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG divideInteger    Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG quotientInteger  Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG remainderInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG modInteger       Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG lessThanInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG lessThanEqualsInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG greaterThanInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG greaterThanEqualsInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG equalsInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  boolean
SIG resizeInteger Γ =
  (Γ ,⋆ # ,⋆ #)
  ,,
  (con size (` Z) ∷ con integer (` (S Z)) ∷ [])
  ,,
  con integer (` Z)
SIG sizeOfInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ []
  ,,
  con size (` Z)
SIG intToByteString Γ =
  Γ ,⋆ # ,⋆ #
  ,,
  con size (` Z) ∷ con integer (` (S Z)) ∷ []
  ,,
  con bytestring (` Z)
SIG concatenate      Γ =
  Γ ,⋆ #
  ,,
  con bytestring (` Z) ∷ con bytestring (` Z) ∷ []
  ,,
  con bytestring (` Z)
SIG takeByteString Γ =
  (Γ ,⋆ #  ,⋆ #)
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG dropByteString Γ =
  (Γ ,⋆ #  ,⋆ #)
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG sha2-256 Γ =
  Γ ,⋆ #
  ,,
  con bytestring (` Z) ∷ []
  ,,
  con bytestring (size⋆ 32)
SIG sha3-256 Γ =
  Γ ,⋆ #
  ,,
  con bytestring (` Z) ∷ []
  ,,
  con bytestring (size⋆ 32)
SIG verifySignature Γ =
  Γ ,⋆ # ,⋆ # ,⋆ #
  ,,
  con bytestring (` (S (S Z)))
    ∷ con bytestring (` (S Z))
    ∷ con bytestring (` Z)
    ∷ []
  ,,
  boolean
SIG resizeByteString Γ =
  Γ ,⋆ # ,⋆ #
  ,,
  con size (` Z) ∷ con bytestring (` (S Z)) ∷ []
  ,,
  con bytestring (` Z)
SIG equalsByteString Γ =
  Γ ,⋆ #
  ,,
  con bytestring (` Z) ∷ con bytestring (` Z) ∷ []
  ,,
  boolean
SIG txh Γ = Γ ,, [] ,, con bytestring (size⋆ 32)
SIG blocknum Γ =
  Γ ,⋆ #
  ,,
  con size (` Z) ∷ []
  ,,
  con integer (` Z)
\end{code}
