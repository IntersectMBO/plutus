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
-}

{- Note [allErrorCodes]
   This list contains all error codes used in the plutus prelude and it is
   important that when an error code is added to the prelude it is also added
   to this list.
-}

-- | A list of all error codes used in the plutus prelude
allErrorCodes :: Map Builtins.BuiltinString String
allErrorCodes =
  Map.fromList
    [ ("PT1", "TH Generation of Indexed Data Error")
    , ("PT2", "Void is not supported")
    , ("PT3", "Ratio number can't have a zero denominator")
    , ("PT4", "'round' got an incorrect input")
    , ("PT5", "'check' input is 'False'")
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
    ]

-- | The error happens in TH generation of indexed data
{-# INLINEABLE reconstructCaseError #-}
reconstructCaseError :: Builtins.BuiltinString
reconstructCaseError = "PT1"

-- | Error case of 'unsafeFromBuiltinData'
{-# INLINEABLE voidIsNotSupportedError #-}
voidIsNotSupportedError :: Builtins.BuiltinString
voidIsNotSupportedError = "PT2"

-- | Ratio number can't have a zero denominator
{-# INLINEABLE ratioHasZeroDenominatorError #-}
ratioHasZeroDenominatorError :: Builtins.BuiltinString
ratioHasZeroDenominatorError = "PT3"

-- | 'round' got an incorrect input
{-# INLINEABLE roundDefaultDefnError #-}
roundDefaultDefnError :: Builtins.BuiltinString
roundDefaultDefnError = "PT4"

-- | 'check' input is 'False'
{-# INLINEABLE checkHasFailedError #-}
checkHasFailedError :: Builtins.BuiltinString
checkHasFailedError = "PT5"

-- | PlutusTx.List.!!: negative index
{-# INLINEABLE negativeIndexError #-}
negativeIndexError :: Builtins.BuiltinString
negativeIndexError = "PT6"

-- | PlutusTx.List.!!: index too large
{-# INLINEABLE indexTooLargeError #-}
indexTooLargeError :: Builtins.BuiltinString
indexTooLargeError = "PT7"

-- | PlutusTx.List.head: empty list
{-# INLINEABLE headEmptyListError #-}
headEmptyListError :: Builtins.BuiltinString
headEmptyListError = "PT8"

-- | PlutusTx.List.tail: empty list
{-# INLINEABLE tailEmptyListError #-}
tailEmptyListError :: Builtins.BuiltinString
tailEmptyListError = "PT9"

-- | PlutusTx.Enum.().succ: bad argument
{-# INLINEABLE succVoidBadArgumentError #-}
succVoidBadArgumentError :: Builtins.BuiltinString
succVoidBadArgumentError = "PT10"

-- | PlutusTx.Enum.().pred: bad argument
{-# INLINEABLE predVoidBadArgumentError #-}
predVoidBadArgumentError :: Builtins.BuiltinString
predVoidBadArgumentError = "PT11"

-- | PlutusTx.Enum.().toEnum: bad argument
{-# INLINEABLE toEnumVoidBadArgumentError #-}
toEnumVoidBadArgumentError :: Builtins.BuiltinString
toEnumVoidBadArgumentError = "PT12"

-- | PlutusTx.Enum.Bool.succ: bad argument
{-# INLINEABLE succBoolBadArgumentError #-}
succBoolBadArgumentError :: Builtins.BuiltinString
succBoolBadArgumentError = "PT13"

-- | PlutusTx.Enum.Bool.pred: bad argument
{-# INLINEABLE predBoolBadArgumentError #-}
predBoolBadArgumentError :: Builtins.BuiltinString
predBoolBadArgumentError = "PT14"

-- | PlutusTx.Enum.Bool.toEnum: bad argument
{-# INLINEABLE toEnumBoolBadArgumentError #-}
toEnumBoolBadArgumentError :: Builtins.BuiltinString
toEnumBoolBadArgumentError = "PT15"

-- | PlutusTx.Enum.Ordering.succ: bad argument
{-# INLINEABLE succOrderingBadArgumentError #-}
succOrderingBadArgumentError :: Builtins.BuiltinString
succOrderingBadArgumentError = "PT16"

-- | PlutusTx.Enum.Ordering.pred: bad argument
{-# INLINEABLE predOrderingBadArgumentError #-}
predOrderingBadArgumentError :: Builtins.BuiltinString
predOrderingBadArgumentError = "PT17"

-- | PlutusTx.Enum.Ordering.toEnum: bad argument
{-# INLINEABLE toEnumOrderingBadArgumentError #-}
toEnumOrderingBadArgumentError :: Builtins.BuiltinString
toEnumOrderingBadArgumentError = "PT18"

-- | PlutusTx.List.last: empty list
{-# INLINEABLE lastEmptyListError #-}
lastEmptyListError :: Builtins.BuiltinString
lastEmptyListError = "PT19"
