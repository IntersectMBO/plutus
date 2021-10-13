{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators         #-}
module Plutus.ChainIndex.Api
  ( API
  , FromHashAPI
  , UtxoAtAddressRequest(..)
  , UtxoWithCurrencyRequest(..)
  ) where

import           Control.Monad.Freer.Extras.Pagination (Page, PageQuery)
import           Data.Aeson                            (FromJSON, ToJSON)
import           GHC.Generics                          (Generic)
import           Ledger                                (AssetClass, Datum, DatumHash, MintingPolicy, MintingPolicyHash,
                                                        Redeemer, RedeemerHash, StakeValidator, StakeValidatorHash,
                                                        TxId, Validator, ValidatorHash)
import           Ledger.Credential                     (Credential)
import           Ledger.Tx                             (ChainIndexTxOut, TxOutRef)
import           Plutus.ChainIndex.Tx                  (ChainIndexTx)
import           Plutus.ChainIndex.Types               (Diagnostics, Tip)
import           Servant.API                           (Get, JSON, NoContent, Post, Put, ReqBody, (:<|>), (:>))

-- | When requesting UTxOs of a given address, you need to provide the address,
-- and optionnally the number of elements per page and the last item of the last
-- requested page.
--
-- Here's an example for requesting the first page:
--
-- {
--   "credential": {
--     "tag": "PubKeyCredential",
--     "contents": {
--       "getPubKeyHash": "88ff402b0522f27649ac742238c697c579beeb344eb723099d1f16ce"
--     }
--   }
-- }
--
-- or
--
-- {
--   "pageQuery": {
--     "pageQuerySize": {
--       "getPageSize": 10
--     }
--   },
--   "credential": {
--     "tag": "PubKeyCredential",
--     "contents": {
--       "getPubKeyHash": "88ff402b0522f27649ac742238c697c579beeb344eb723099d1f16ce"
--     }
--   }
-- }
--
-- Here's an example for requesting the next page:
--
-- {
--   "pageQuery": {
--     "pageQuerySize": {
--       "getPageSize": 10
--     },
--     "pageQueryLastItem": {
--       "txOutRefId": {
--         "getTxId": "009b8c674b878cc68bd1d40562c5f14cdbb21be9266f605cfb68ed978e1a965b"
--       },
--       "txOutRefIdx": 0
--     }
--   },
--   "credential": {
--     "tag": "PubKeyCredential",
--     "contents": {
--       "getPubKeyHash": "88ff402b0522f27649ac742238c697c579beeb344eb723099d1f16ce"
--     }
--   }
-- }
data UtxoAtAddressRequest = UtxoAtAddressRequest
    { pageQuery  :: Maybe (PageQuery TxOutRef)
    , credential :: Credential
    }
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

-- | See the comment on 'UtxoAtAddressRequest'.
--
-- The difference is using @currency@ field instead of @credential@.
-- {
--   "pageQuery": {
--     ...
--   },
--   "currency": {
--     "unAssetClass": [
--       {
--         "unCurrencySymbol": ""
--       },
--       {
--         "unTokenName": ""
--       }
--     ]
--   }
-- }
data UtxoWithCurrencyRequest = UtxoWithCurrencyRequest
    { pageQuery :: Maybe (PageQuery TxOutRef)
    , currency  :: AssetClass
    }
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

type API
    = "healthcheck" :> Get '[JSON] NoContent
    :<|> "from-hash" :> FromHashAPI
    :<|> "tx-out" :> ReqBody '[JSON] TxOutRef :> Post '[JSON] ChainIndexTxOut
    :<|> "tx" :> ReqBody '[JSON] TxId :> Post '[JSON] ChainIndexTx
    :<|> "is-utxo" :> ReqBody '[JSON] TxOutRef :> Post '[JSON] (Tip, Bool)
    :<|> "utxo-at-address" :> ReqBody '[JSON] UtxoAtAddressRequest :> Post '[JSON] (Tip, Page TxOutRef)
    :<|> "utxo-with-currency" :> ReqBody '[JSON] UtxoWithCurrencyRequest :> Post '[JSON] (Tip, Page TxOutRef)
    :<|> "tip" :> Get '[JSON] Tip
    :<|> "collect-garbage" :> Put '[JSON] NoContent
    :<|> "diagnostics" :> Get '[JSON] Diagnostics

type FromHashAPI =
    "datum" :> ReqBody '[JSON] DatumHash :> Post '[JSON] Datum
    :<|> "validator" :> ReqBody '[JSON] ValidatorHash :> Post '[JSON] Validator
    :<|> "minting-policy" :> ReqBody '[JSON] MintingPolicyHash :> Post '[JSON] MintingPolicy
    :<|> "stake-validator" :> ReqBody '[JSON] StakeValidatorHash :> Post '[JSON] StakeValidator
    :<|> "redeemer" :> ReqBody '[JSON] RedeemerHash :> Post '[JSON] Redeemer
