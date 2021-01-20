{-# LANGUAGE NamedFieldPuns #-}
-- | Dealing with tokens
module Ledger.Tokens(
  -- $tokens
  token
  , outputsWith
  , paidTo
  ) where

import           Plutus.V1.Ledger.Contexts
import           Plutus.V1.Ledger.Value    (CurrencySymbol, TokenName, Value, leq)
import qualified Plutus.V1.Ledger.Value    as Value

-- $tokens
-- The extended UTXO ledger with scripts that Plutus runs on supports
-- native user-defined currencies. Tokens are user-defined currencies
-- with an issuance of exactly one unit. Every token is identified by
-- a pair of 'CurrencySymbol' and 'TokenName'.
-- To create a token use the

{-# INLINABLE token #-}
-- | A value that contains exactly the token.
token :: CurrencySymbol -> TokenName -> Value
token symbol name = Value.singleton symbol name 1

{-# INLINABLE outputsWith #-}
-- | The outputs of the 'ValidatorCtx' that carry a non-zero amount of the currency
--   defined by the 'CurrencySymbol' and the 'TokenName'.
outputsWith :: TxInfo -> CurrencySymbol -> TokenName -> [TxOut]
outputsWith TxInfo{txInfoOutputs} symbol name =
    filter (\output -> token symbol name  `leq` txOutValue output) txInfoOutputs

{-# INLINABLE paidTo #-}
-- | The total 'Value' paid by the pending transaction to outputs
--   whose value also includes a non-zero amount of the currency
--   & token
paidTo :: TxInfo -> CurrencySymbol -> TokenName -> Value
paidTo ptx symbol name =
    foldMap txOutValue (outputsWith ptx symbol name)
