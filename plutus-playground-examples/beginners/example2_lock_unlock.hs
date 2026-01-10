{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LockUnlock where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts
import Prelude (IO)

{-# INLINABLE mkValidator #-}
mkValidator :: BuiltinByteString -> BuiltinByteString -> BuiltinData -> ()
mkValidator expected actual _ =
    if expected == actual
        then ()
        else error ()

validator :: Validator
validator =
    mkValidatorScript $$(PlutusTx.compile
        [||
            mkValidator
        ||]
    )
