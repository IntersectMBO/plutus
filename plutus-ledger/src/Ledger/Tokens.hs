{-# LANGUAGE NamedFieldPuns #-}
-- | Dealing with tokens
module Ledger.Tokens(
  -- $tokens
  token
  , outputsWith
  , paidTo
  ) where

import           Plutus.V1.Ledger.Contexts
import           Plutus.V1.Ledger.Value    (Currency, Value, leq)
import qualified Plutus.V1.Ledger.Value    as Value

-- $tokens
-- The extended UTXO ledger with scripts that Plutus runs on supports
-- native user-defined currencies. Tokens are user-defined currencies
-- with an issuance of exactly one unit. Every token is identified by
-- a 'Currency'.

{-# INLINABLE token #-}
-- | A value that contains exactly the token.
token :: Currency -> Value
token cur = Value.currencyValue cur 1

{-# INLINABLE outputsWith #-}
-- | The outputs of the 'ValidatorCtx' that carry a non-zero amount of the
--   currency.
outputsWith :: TxInfo -> Currency -> [TxOut]
outputsWith TxInfo{txInfoOutputs} currency =
    filter (\output -> token currency  `leq` txOutValue output) txInfoOutputs

{-# INLINABLE paidTo #-}
-- | The total 'Value' paid by the pending transaction to outputs
--   whose value also includes a non-zero amount of the currency.
paidTo :: TxInfo -> Currency -> Value
paidTo ptx currency =
    foldMap txOutValue (outputsWith ptx currency)
