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
  concatenate              : Builtin
  takeByteString           : Builtin
  dropByteString           : Builtin
  sha2-256                 : Builtin
  sha3-256                 : Builtin
  verifySignature          : Builtin
  equalsByteString         : Builtin
  ifThenElse               : Builtin

{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC Builtin = data BuiltinName (AddInteger | SubtractInteger | MultiplyInteger | DivideInteger | QuotientInteger | RemainderInteger | ModInteger | LessThanInteger | LessThanEqInteger | GreaterThanInteger | GreaterThanEqInteger | EqInteger | Concatenate | TakeByteString | DropByteString | SHA2 | SHA3 | VerifySignature | EqByteString | IfThenElse) #-}
\end{code}
