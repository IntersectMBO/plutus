{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeOperators              #-}

module Playground.API where

import           Control.Arrow              (left)
import           Data.Aeson                 (FromJSON (parseJSON), ToJSON (toJSON), Value, withText)
import qualified Data.Aeson                 as JSON
import qualified Data.ByteString.Base64     as Base64
import           Data.ByteString.Lazy       (fromStrict, toStrict)
import           Data.Map                   (Map)
import           Data.Swagger               (Schema, ToSchema)
import           Data.Text                  (Text)
import           Data.Text.Encoding         (decodeUtf8, decodeUtf8', encodeUtf8)
import           GHC.Generics               (Generic)
import qualified Language.Haskell.TH.Syntax as TH
import           Network.HTTP.Media         ((//), (/:))
import           Servant.API                ((:<|>), (:>), Accept (contentType), Capture, JSON, MimeRender (mimeRender),
                                             MimeUnrender (mimeUnrender), NoContent, Post, ReqBody)
import           Wallet.Emulator.Types      (Wallet)
import           Wallet.UTXO.Types          (Blockchain)

type API
   = "contract" :> ReqBody '[ Haskell] SourceCode :> Post '[ JSON] [FunctionSchema]
     :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] Blockchain

newtype Haskell = Haskell Text
  deriving stock (Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Accept Haskell where
  contentType _ = "application" // "x-haskell" /: ("charset", "utf-8")

newtype SourceCode = SourceCode {getSourceCode :: Text}
  deriving stock (Generic)

instance ToJSON SourceCode where
  toJSON (SourceCode t) = JSON.String . decodeUtf8 . Base64.encode . encodeUtf8 $ t

instance FromJSON SourceCode where
  parseJSON = withText "SourceCode" $ \t -> do
    let eRes = Base64.decode . encodeUtf8 $ t
    case eRes of
      Left e  -> fail "not a valid Base64 encoded String"
      Right v -> pure . SourceCode . decodeUtf8  $ v

instance MimeRender Haskell SourceCode where
  mimeRender _ (SourceCode t) = fromStrict (encodeUtf8 t)

instance MimeUnrender Haskell SourceCode where
  mimeUnrender _ = left show . fmap SourceCode . decodeUtf8' . toStrict

newtype FunctionsSchema = FunctionsSchema [(Fn, Text)]
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)

newtype Fn = Fn Text
  deriving stock (Show, Generic, TH.Lift)
  deriving newtype (ToJSON, FromJSON)

data Expression = Expression
  { function  :: Fn
  , wallet    :: Wallet
  , arguments :: [Value]
  }
  deriving (Generic, ToJSON, FromJSON)

type Program = [Expression]

data Evaluation = Evaluation
  { wallets    :: [(Wallet, Integer)]
  , program    :: Program
  , sourceCode :: SourceCode
  , blockchain :: Blockchain
  }
  deriving (Generic, ToJSON, FromJSON)

data FunctionSchema = FunctionSchema
  { functionName   :: Fn
  , argumentSchema :: [Schema]
  }
  deriving (Show, Generic, ToJSON)
