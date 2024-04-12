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
plutusPreludeErrorCodes = Map.fromDistinctAscList
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
{-# INLINABLE reconstructCaseError #-}
reconstructCaseError :: Builtins.BuiltinString
reconstructCaseError = "PT1"

-- | Error case of 'unsafeFromBuiltinData'
{-# INLINABLE voidIsNotSupportedError #-}
voidIsNotSupportedError :: Builtins.BuiltinString
voidIsNotSupportedError = "PT2"

-- | Ratio number can't have a zero denominator
{-# INLINABLE ratioHasZeroDenominatorError #-}
ratioHasZeroDenominatorError :: Builtins.BuiltinString
ratioHasZeroDenominatorError = "PT3"

-- | 'check' input is 'False'
{-# INLINABLE checkHasFailedError #-}
checkHasFailedError :: Builtins.BuiltinString
checkHasFailedError = "PT5"

-- | PlutusTx.List.!!: negative index
{-# INLINABLE negativeIndexError #-}
negativeIndexError :: Builtins.BuiltinString
negativeIndexError = "PT6"

-- | PlutusTx.List.!!: index too large
{-# INLINABLE indexTooLargeError #-}
indexTooLargeError :: Builtins.BuiltinString
indexTooLargeError = "PT7"

-- | PlutusTx.List.head: empty list
{-# INLINABLE headEmptyListError #-}
headEmptyListError :: Builtins.BuiltinString
headEmptyListError = "PT8"

-- | PlutusTx.List.tail: empty list
{-# INLINABLE tailEmptyListError #-}
tailEmptyListError :: Builtins.BuiltinString
tailEmptyListError = "PT9"

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

-- | PlutusTx.List.last: empty list
{-# INLINABLE lastEmptyListError #-}
lastEmptyListError :: Builtins.BuiltinString
lastEmptyListError = "PT19"

-- | PlutusTx.Ratio.recip: reciprocal of zero
{-# INLINABLE reciprocalOfZeroError #-}
reciprocalOfZeroError :: Builtins.BuiltinString
reciprocalOfZeroError = "PT20"

-- | PlutusTx.List.indexBuiltinList: negative index
{-# INLINABLE builtinListNegativeIndexError #-}
builtinListNegativeIndexError :: Builtins.BuiltinString
builtinListNegativeIndexError = "PT21"

-- | PlutusTx.List.indexBuiltinList: index too large
{-# INLINABLE builtinListIndexTooLargeError #-}
builtinListIndexTooLargeError :: Builtins.BuiltinString
builtinListIndexTooLargeError = "PT22"
