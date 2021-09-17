{-# LANGUAGE OverloadedStrings #-}
module PlutusTx.ErrorCodes where

import           PlutusTx.Builtins as Builtins

-- | The error happens in TH generation of indexed data
reconstructCaseError :: Builtins.BuiltinString
reconstructCaseError = "PT01"

-- | Error case of 'unsafeFromBuiltinData'
voidIsNotSupportedError :: Builtins.BuiltinString
voidIsNotSupportedError = "PT02"
