{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}

module API where

import           Data.Aeson             (FromJSON, ToJSON, Value)
import qualified Data.ByteString.Lazy   as BS
import           Data.Map               (Map)
import           Data.Text              (Text)
import           GHC.Generics           (Generic)
import           Language.Marlowe       (Contract, Input, State, TransactionInput, TransactionWarning)
import           Ledger                 (PubKeyHash (..))
import           Network.HTTP.Media     ((//), (/:))
import           Plutus.V1.Ledger.Value (CurrencySymbol (..), TokenName (..))
import           Servant.API            (Accept (..), Capture, EmptyAPI, Get, Header, JSON, MimeRender (..), NoContent,
                                         PlainText, Post, Raw, ReqBody, (:<|>), (:>))

instance Accept HTML where
  contentType _ = "text" // "html" /: ("charset", "utf-8")
newtype RawHtml = RawHtml { unRaw :: BS.ByteString }

data HTML = HTML

instance MimeRender HTML RawHtml where
    mimeRender _ =  unRaw

type PrivateKey = String

type PublicKey = String

data TransferRequest = TransferRequest { src_priv_key    :: PrivateKey
                                       , currency_symbol :: CurrencySymbol
                                       , token_symbol    :: TokenName
                                       , amount          :: Integer
                                       , dest_pub_key    :: PubKeyHash
                                       }
  deriving (Generic, FromJSON)

data CreateContractRequest = CreateContractRequest { creator_priv_key  :: PrivateKey
                                                   , role_distribution :: [(TokenName, PubKeyHash)]
                                                   , contract          :: Contract
                                                   }
  deriving (Generic, FromJSON)

data GetContractStateResponse = GetContractStateResponse { curr_state    :: State
                                                         , curr_contract :: Contract
                                                         }
  deriving (Generic, Show, ToJSON)

data GetContractHistoryResponse = GetContractHistoryResponse { original_state    :: State
                                                             , original_contract :: Contract
                                                             , inputs            :: [TransactionInput]
                                                             }
  deriving (Generic, Show, ToJSON)

data ApplyInputRequest = ApplyInputRequest { signing_priv_key         :: PrivateKey
                                           , contract_currency_symbol :: CurrencySymbol
                                           , input_to_apply           :: TransactionInput
                                           }
  deriving (Generic, FromJSON)


type JSON_API = "create_wallet" :> ReqBody '[JSON] PrivateKey :> Post '[JSON] PublicKey :<|>
                "list_wallet_funds" :> ReqBody '[JSON] PublicKey :> Post '[JSON] (Map CurrencySymbol [(TokenName, Integer)]) :<|>
                "transfer_funds" :> ReqBody '[JSON] TransferRequest :> Post '[JSON] () :<|>
                "create_contract" :> ReqBody '[JSON] CreateContractRequest :> Post '[JSON] (Either String CurrencySymbol) :<|>
                "get_contract_state" :> ReqBody '[JSON] CurrencySymbol :> Post '[JSON] GetContractStateResponse :<|>
                "get_contract_history" :> ReqBody '[JSON] CurrencySymbol :> Post '[JSON] GetContractHistoryResponse :<|>
                "apply_input" :> ReqBody '[JSON] ApplyInputRequest :> Post '[JSON] (Either String [TransactionWarning])


type PLAIN_API = "create_wallet" :> Capture "priv_key" String :> Get '[PlainText] String :<|>
                 "list_wallet_funds" :> Capture "pub_key" String :> Get '[PlainText] String :<|>
                 "transfer_funds" :> Capture "src_priv_key" String :> Capture "currency_symbol" String
                                  :> Capture "token_symbol" String :> Capture "amount" Integer
                                  :> Capture "dest_pub_key" String :> Get '[PlainText] String :<|>
                 "create_contract" :> Capture "creator_priv_key" String :> Capture "role_distribution" String
                                   :> Capture "contract" String :> Get '[PlainText] String :<|>
                 "get_contract_state" :> Capture "contract_state" String :> Get '[PlainText] String :<|>
                 "get_contract_history" :> Capture "contract_history" String :> Get '[PlainText] String :<|>
                 "apply_input" :> Capture "signing_priv_key" String :> Capture "contract_currency_symbol" String
                               :> Capture "transaction_input" String :> Get '[PlainText] String

type STATIC = Raw
type API = JSON_API :<|>
           PLAIN_API :<|>
           "test" :> Get '[HTML] RawHtml :<|>
            Raw

