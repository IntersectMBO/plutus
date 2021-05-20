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
                                       , dest_pub_key    :: PublicKey}
  deriving (Generic, FromJSON)

type JSON_API = "create_wallet" :> ReqBody '[JSON] PrivateKey :> Post '[JSON] PublicKey :<|>
                "list_wallet_funds" :> ReqBody '[JSON] PublicKey :> Post '[JSON] (Map CurrencySymbol [(TokenName, Integer)]) :<|>
                "transfer_funds" :> ReqBody '[JSON] TransferRequest :> Post '[JSON] ()


type PLAIN_API = "create_wallet" :> Capture "priv_key" String :> Get '[PlainText] String :<|>
                 "list_wallet_funds" :> Capture "pub_key" String :> Get '[PlainText] String :<|>
                 "transfer_funds" :> Capture "src_priv_key" String :> Capture "currency_symbol" String
                                  :> Capture "token_symbol" String :> Capture "amount" Integer
                                  :> Capture "dest_pub_key" String :> Get '[PlainText] String

type STATIC = Raw
type API = JSON_API :<|>
           PLAIN_API :<|>
           "test" :> Get '[HTML] RawHtml :<|>
            Raw

