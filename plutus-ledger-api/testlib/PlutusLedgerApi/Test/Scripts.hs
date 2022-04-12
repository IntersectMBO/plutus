module PlutusLedgerApi.Test.Scripts
    (-- * Example scripts
    unitRedeemer,
    unitDatum
    ) where

import PlutusLedgerApi.V1.Scripts
import PlutusTx

-- | @()@ as a datum.
unitDatum :: Datum
unitDatum = Datum $ toBuiltinData ()

-- | @()@ as a redeemer.
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $ toBuiltinData ()

