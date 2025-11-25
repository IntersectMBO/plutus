{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module DonationValidator where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts
import Prelude (IO)

{-# INLINABLE mkValidator #-}
mkValidator :: PubKeyHash -> BuiltinData -> BuiltinData -> ScriptContext -> ()
mkValidator pkh _ _ ctx =
    if txSignedBy (scriptContextTxInfo ctx) pkh
        then ()
        else error ()

validator :: PubKeyHash -> Validator
validator pkh =
    mkValidatorScript $$(PlutusTx.compile
        [||
            mkValidator
        ||]
    )
