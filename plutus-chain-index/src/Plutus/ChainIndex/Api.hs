{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Plutus.ChainIndex.Api(API, FromHashAPI) where

import           Ledger                  (Datum, DatumHash, MintingPolicy, MintingPolicyHash, Redeemer, RedeemerHash,
                                          StakeValidator, StakeValidatorHash, TxId, Validator, ValidatorHash)
import           Ledger.Credential       (Credential)
import           Ledger.Tx               (ChainIndexTxOut, TxOutRef)
import           Plutus.ChainIndex.Tx    (ChainIndexTx)
import           Plutus.ChainIndex.Types (Diagnostics, Page, Tip)
import           Servant.API             (Get, JSON, NoContent, Post, Put, ReqBody, (:<|>), (:>))

type API
    = "healthcheck" :> Get '[JSON] NoContent
    :<|> "from-hash" :> FromHashAPI
    :<|> "tx-out" :> ReqBody '[JSON] TxOutRef :> Post '[JSON] ChainIndexTxOut
    :<|> "tx" :> ReqBody '[JSON] TxId :> Post '[JSON] ChainIndexTx
    :<|> "is-utxo" :> ReqBody '[JSON] TxOutRef :> Post '[JSON] (Tip, Bool)
    :<|> "utxo-at-address" :> ReqBody '[JSON] Credential :> Post '[JSON] (Tip, Page TxOutRef)
    :<|> "tip" :> Get '[JSON] Tip
    :<|> "collect-garbage" :> Put '[JSON] NoContent
    :<|> "diagnostics" :> Get '[JSON] Diagnostics

type FromHashAPI =
    "datum" :> ReqBody '[JSON] DatumHash :> Post '[JSON] Datum
    :<|> "validator" :> ReqBody '[JSON] ValidatorHash :> Post '[JSON] Validator
    :<|> "minting-policy" :> ReqBody '[JSON] MintingPolicyHash :> Post '[JSON] MintingPolicy
    :<|> "stake-validator" :> ReqBody '[JSON] StakeValidatorHash :> Post '[JSON] StakeValidator
    :<|> "redeemer" :> ReqBody '[JSON] RedeemerHash :> Post '[JSON] Redeemer
