{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}

module Playground.API where

import           Control.Arrow        (left)
import           Data.Aeson           (FromJSON, ToJSON, Value)
import           Data.ByteString.Lazy (fromStrict, toStrict)
import           Data.Text            (Text)
import           Data.Text.Encoding   (decodeUtf8', encodeUtf8)
import           Network.HTTP.Media   ((//), (/:))
import           Servant.API          ((:<|>), (:>), Accept (contentType), Capture, JSON, MimeRender (mimeRender),
                                       MimeUnrender (mimeUnrender), NoContent, Post, ReqBody)
import           Wallet.UTXO.Types    (Blockchain)
import Data.Map (Map)
import Wallet.Emulator.Types (Wallet)
import GHC.Generics (Generic)

type API
   = "contract" :> ReqBody '[ Haskell] SourceCode :> Post '[ JSON] NoContent
     :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] Blockchain

data Haskell

instance Accept Haskell where
  contentType _ = "application" // "x-haskell" /: ("charset", "utf-8")

newtype SourceCode =
  SourceCode Text

instance MimeRender Haskell SourceCode where
  mimeRender _ (SourceCode t) = fromStrict (encodeUtf8 t)

instance MimeUnrender Haskell SourceCode where
  mimeUnrender _ = left show . fmap SourceCode . decodeUtf8' . toStrict

newtype Fx = Fx Text
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)

data Evaluation = Evaluation { wallets :: (Wallet, Integer)
                                , functions :: [(Fx, Value)]
                                }
  deriving (Generic, ToJSON, FromJSON)
