\begin{code}
module Builtin where


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
\end{code}
