{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeOperators              #-}

module Playground.API where

import           Control.Arrow              (left)
import           Control.Newtype.Generics   (Newtype)
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
   = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] [FunctionSchema]
     :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] Blockchain

newtype SourceCode = SourceCode Text
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)
  deriving anyclass (Newtype)

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
