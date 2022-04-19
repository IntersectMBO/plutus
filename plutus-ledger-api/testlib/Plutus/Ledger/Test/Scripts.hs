module Plutus.Ledger.Test.Scripts
    (-- * Example scripts
    unitRedeemer,
    unitDatum
    ) where

import Plutus.V1.Ledger.Scripts
import PlutusTx

-- | @()@ as a datum.
unitDatum :: Datum
unitDatum = Datum $ toBuiltinData ()

-- | @()@ as a redeemer.
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $ toBuiltinData ()

