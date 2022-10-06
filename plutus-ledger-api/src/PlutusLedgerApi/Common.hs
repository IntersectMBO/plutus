-- | Common types and functions used across all the ledger API modules.
module PlutusLedgerApi.Common
    -- There is a reason for not using the `as Export` trick: it makes haddock ugly/verbose
    ( module PlutusLedgerApi.Common.Eval
    , module PlutusLedgerApi.Common.SerialisedScript
    , module PlutusLedgerApi.Common.Versions
    , module PlutusLedgerApi.Common.Address
    , module PlutusLedgerApi.Common.Bytes
    , module PlutusLedgerApi.Common.Credential
    , module PlutusLedgerApi.Common.Crypto
    , module PlutusLedgerApi.Common.DCert
    , module PlutusLedgerApi.Common.Interval
    , module PlutusLedgerApi.Common.Scripts
    , module PlutusLedgerApi.Common.Time
    , module PlutusLedgerApi.Common.Value
    ) where

import PlutusLedgerApi.Common.Eval
import PlutusLedgerApi.Common.SerialisedScript
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.Common.Address
import PlutusLedgerApi.Common.Bytes
import PlutusLedgerApi.Common.Credential
import PlutusLedgerApi.Common.Crypto
import PlutusLedgerApi.Common.DCert
import PlutusLedgerApi.Common.Interval
import PlutusLedgerApi.Common.Scripts
import PlutusLedgerApi.Common.Time
import PlutusLedgerApi.Common.Value


{- Note [Abstract types in the ledger API]
We need to support old versions of the ledger API as we update the code that it depends on. You
might think that we should therefore make the types that we expose abstract, and only expose
specific functions for constructing and working with them. However the situation is slightly
different for us.

Normally, when you are in this situation, you want to retain the same *interface* as the old version,
but with the new types and functions underneath. Abstraction lets you do this easily. But we actually
want to keep the old *implementation*, because things really have to work the same, bug-for-bug. And
the types have to translate into Plutus Core in exactly the same way, and so on.

So we're going to end up with multiple versions of the types and functions that we expose here, even
internally. That means we don't lose anything by exposing all the details: we're never going to remove
anything, we're just going to create new versions.
-}
