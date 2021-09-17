{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.ErrorCodes where

import           PlutusTx.Builtins as Builtins

{-
All error codes in this module should be unique and can be used only once!
They help to trace the errors in on-chain code.
-}

-- | The error happens in TH generation of indexed data
{-# INLINABLE reconstructCaseError #-}
reconstructCaseError :: Builtins.BuiltinString
reconstructCaseError = "PT01"

-- | Error case of 'unsafeFromBuiltinData'
{-# INLINABLE voidIsNotSupportedError #-}
voidIsNotSupportedError :: Builtins.BuiltinString
voidIsNotSupportedError = "PT02"

-- | Ratio number can't have a zero denominator
{-# INLINABLE ratioHasZeroDenominatorError #-}
ratioHasZeroDenominatorError :: Builtins.BuiltinString
ratioHasZeroDenominatorError = "PT03"

-- | 'round' got an incorrect input
{-# INLINABLE roundDefaultDefnError #-}
roundDefaultDefnError :: Builtins.BuiltinString
roundDefaultDefnError = "PT04"

-- | 'check' input is 'False'
{-# INLINABLE checkHasFailedError #-}
checkHasFailedError :: Builtins.BuiltinString
checkHasFailedError = "PT05"

-- | PlutusTx.List.!!: negative index
{-# INLINABLE negativeIndexError #-}
negativeIndexError :: Builtins.BuiltinString
negativeIndexError = "PT06"

-- | PlutusTx.List.!!: index too large
{-# INLINABLE indexTooLargeError #-}
indexTooLargeError :: Builtins.BuiltinString
indexTooLargeError = "PT07"

-- | PlutusTx.List.head: empty list
{-# INLINABLE headEmptyListError #-}
headEmptyListError :: Builtins.BuiltinString
headEmptyListError = "PT08"

-- | PlutusTx.List.tail: empty list
{-# INLINABLE tailEmptyListError #-}
tailEmptyListError :: Builtins.BuiltinString
tailEmptyListError = "PT09"

-- | PlutusTx.Enum.().succ: bad argument
{-# INLINABLE succVoidBadArgumentError #-}
succVoidBadArgumentError :: Builtins.BuiltinString
succVoidBadArgumentError = "PT10"

-- | PlutusTx.Enum.().pred: bad argument
{-# INLINABLE predVoidBadArgumentError #-}
predVoidBadArgumentError :: Builtins.BuiltinString
predVoidBadArgumentError = "PT11"

-- | PlutusTx.Enum.().toEnum: bad argument
{-# INLINABLE toEnumVoidBadArgumentError #-}
toEnumVoidBadArgumentError :: Builtins.BuiltinString
toEnumVoidBadArgumentError = "PT12"

-- | PlutusTx.Enum.Bool.succ: bad argument
{-# INLINABLE succBoolBadArgumentError #-}
succBoolBadArgumentError :: Builtins.BuiltinString
succBoolBadArgumentError = "PT13"

-- | PlutusTx.Enum.Bool.pred: bad argument
{-# INLINABLE predBoolBadArgumentError #-}
predBoolBadArgumentError :: Builtins.BuiltinString
predBoolBadArgumentError = "PT14"

-- | PlutusTx.Enum.Bool.toEnum: bad argument
{-# INLINABLE toEnumBoolBadArgumentError #-}
toEnumBoolBadArgumentError :: Builtins.BuiltinString
toEnumBoolBadArgumentError = "PT15"

-- | PlutusTx.Enum.Ordering.succ: bad argument
{-# INLINABLE succOrderingBadArgumentError #-}
succOrderingBadArgumentError :: Builtins.BuiltinString
succOrderingBadArgumentError = "PT16"

-- | PlutusTx.Enum.Ordering.pred: bad argument
{-# INLINABLE predOrderingBadArgumentError #-}
predOrderingBadArgumentError :: Builtins.BuiltinString
predOrderingBadArgumentError = "PT17"

-- | PlutusTx.Enum.Ordering.toEnum: bad argument
{-# INLINABLE toEnumOrderingBadArgumentError #-}
toEnumOrderingBadArgumentError :: Builtins.BuiltinString
toEnumOrderingBadArgumentError = "PT18"
