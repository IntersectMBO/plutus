{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.ErrorCodes where

import Data.Map (Map)
import Data.Map qualified as Map
import PlutusTx.Builtins as Builtins
import Prelude (String)

{-
All error codes in this module should be unique and can be used only once!
They help to trace the errors in on-chain code.

Error codes (e.g. "PT1") become a part of the compiled contract contributing to its size,
therefore we keep them short; On the other hand, the error description isn't part of the
compiled contract, so it doesn't have to be minimal, just short enough, clear and informative.

Adding new error codes should be done without changing the existing ones:
- Add a new error code to the list `plutusPreludeErrorCodes` by incrementing the last error code.
- Add a new function with the error code name and a human-readable description.
- Update the `troubleshooting.rst` file with the new error code and its description.

When writing a new error description please follow existing patterns:
  - If an error is expected to be thrown in a specific function,
    use the fully qualified name of the function.
  - Describe the invariant which is failed.
  - Avoid using the word "error" in the description as it is redundant.
-}

{- Note [plutusPreludeErrorCodes]
   This list contains all error codes used in the plutus prelude and it is
   important that when an error code is added to the prelude it is also added
   to this list.
-}

-- | All error codes used in the plutus prelude associated with a human-readable description.
plutusPreludeErrorCodes :: Map Builtins.BuiltinString String
plutusPreludeErrorCodes = Map.fromList
  [ ("PT1", "TH Generation of Indexed Data Error")
  , ("PT2", "PlutusTx.IsData.Class.unsafeFromBuiltinData: Void is not supported")
  , ("PT3", "PlutusTx.Ratio: zero denominator")
  , ("PT5", "PlutusTx.Prelude.check: input is 'False'")
  , ("PT6", "PlutusTx.List.!!: negative index")
  , ("PT7", "PlutusTx.List.!!: index too large")
  , ("PT8", "PlutusTx.List.head: empty list")
  , ("PT9", "PlutusTx.List.tail: empty list")
  , ("PT10", "PlutusTx.Enum.().succ: bad argument")
  , ("PT11", "PlutusTx.Enum.().pred: bad argument")
  , ("PT12", "PlutusTx.Enum.().toEnum: bad argument")
  , ("PT13", "PlutusTx.Enum.Bool.succ: bad argument")
  , ("PT14", "PlutusTx.Enum.Bool.pred: bad argument")
  , ("PT15", "PlutusTx.Enum.Bool.toEnum: bad argument")
  , ("PT16", "PlutusTx.Enum.Ordering.succ: bad argument")
  , ("PT17", "PlutusTx.Enum.Ordering.pred: bad argument")
  , ("PT18", "PlutusTx.Enum.Ordering.toEnum: bad argument")
  , ("PT19", "PlutusTx.List.last: empty list")
  , ("PT20", "PlutusTx.Ratio.recip: reciprocal of zero")
  , ("PT21", "PlutusTx.List.indexBuiltinList: negative index")
  , ("PT22", "PlutusTx.List.indexBuiltinList: index too large")
  ]

-- | The error happens in TH generation of indexed data
reconstructCaseError :: Builtins.BuiltinString
reconstructCaseError = "PT1"
{-# INLINABLE reconstructCaseError #-}

-- | Error case of 'unsafeFromBuiltinData'
voidIsNotSupportedError :: Builtins.BuiltinString
voidIsNotSupportedError = "PT2"
{-# INLINABLE voidIsNotSupportedError #-}

-- | Ratio number can't have a zero denominator
ratioHasZeroDenominatorError :: Builtins.BuiltinString
ratioHasZeroDenominatorError = "PT3"
{-# INLINABLE ratioHasZeroDenominatorError #-}

-- | 'check' input is 'False'
checkHasFailedError :: Builtins.BuiltinString
checkHasFailedError = "PT5"
{-# INLINABLE checkHasFailedError #-}

-- | PlutusTx.List.!!: negative index
negativeIndexError :: Builtins.BuiltinString
negativeIndexError = "PT6"
{-# INLINABLE negativeIndexError #-}

-- | PlutusTx.List.!!: index too large
indexTooLargeError :: Builtins.BuiltinString
indexTooLargeError = "PT7"
{-# INLINABLE indexTooLargeError #-}

-- | PlutusTx.List.head: empty list
headEmptyListError :: Builtins.BuiltinString
headEmptyListError = "PT8"
{-# INLINABLE headEmptyListError #-}

-- | PlutusTx.List.tail: empty list
tailEmptyListError :: Builtins.BuiltinString
tailEmptyListError = "PT9"
{-# INLINABLE tailEmptyListError #-}

-- | PlutusTx.Enum.().succ: bad argument
succVoidBadArgumentError :: Builtins.BuiltinString
succVoidBadArgumentError = "PT10"
{-# INLINABLE succVoidBadArgumentError #-}

-- | PlutusTx.Enum.().pred: bad argument
predVoidBadArgumentError :: Builtins.BuiltinString
predVoidBadArgumentError = "PT11"
{-# INLINABLE predVoidBadArgumentError #-}

-- | PlutusTx.Enum.().toEnum: bad argument
toEnumVoidBadArgumentError :: Builtins.BuiltinString
toEnumVoidBadArgumentError = "PT12"
{-# INLINABLE toEnumVoidBadArgumentError #-}

-- | PlutusTx.Enum.Bool.succ: bad argument
succBoolBadArgumentError :: Builtins.BuiltinString
succBoolBadArgumentError = "PT13"
{-# INLINABLE succBoolBadArgumentError #-}

-- | PlutusTx.Enum.Bool.pred: bad argument
predBoolBadArgumentError :: Builtins.BuiltinString
predBoolBadArgumentError = "PT14"
{-# INLINABLE predBoolBadArgumentError #-}

-- | PlutusTx.Enum.Bool.toEnum: bad argument
toEnumBoolBadArgumentError :: Builtins.BuiltinString
toEnumBoolBadArgumentError = "PT15"
{-# INLINABLE toEnumBoolBadArgumentError #-}

-- | PlutusTx.Enum.Ordering.succ: bad argument
succOrderingBadArgumentError :: Builtins.BuiltinString
succOrderingBadArgumentError = "PT16"
{-# INLINABLE succOrderingBadArgumentError #-}

-- | PlutusTx.Enum.Ordering.pred: bad argument
predOrderingBadArgumentError :: Builtins.BuiltinString
predOrderingBadArgumentError = "PT17"
{-# INLINABLE predOrderingBadArgumentError #-}

-- | PlutusTx.Enum.Ordering.toEnum: bad argument
toEnumOrderingBadArgumentError :: Builtins.BuiltinString
toEnumOrderingBadArgumentError = "PT18"
{-# INLINABLE toEnumOrderingBadArgumentError #-}

-- | PlutusTx.List.last: empty list
lastEmptyListError :: Builtins.BuiltinString
lastEmptyListError = "PT19"
{-# INLINABLE lastEmptyListError #-}

-- | PlutusTx.Ratio.recip: reciprocal of zero
reciprocalOfZeroError :: Builtins.BuiltinString
reciprocalOfZeroError = "PT20"
{-# INLINABLE reciprocalOfZeroError #-}

-- | PlutusTx.List.indexBuiltinList: negative index
builtinListNegativeIndexError :: Builtins.BuiltinString
builtinListNegativeIndexError = "PT21"
{-# INLINABLE builtinListNegativeIndexError #-}

-- | PlutusTx.List.indexBuiltinList: index too large
builtinListIndexTooLargeError :: Builtins.BuiltinString
builtinListIndexTooLargeError = "PT22"
{-# INLINABLE builtinListIndexTooLargeError #-}
