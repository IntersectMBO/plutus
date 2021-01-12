{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}

module Cardano.ChainIndex.Types where

import           Control.Lens               (makeLenses)
import           Control.Monad.Freer.Log    (LogMessage)
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Sequence              (Seq)
import           GHC.Generics               (Generic)
import           Servant.Client             (BaseUrl)

import           Cardano.Node.Types         (FollowerID)
import           Wallet.Emulator.ChainIndex (ChainIndexEvent, ChainIndexState)

data AppState =
    AppState
        { _indexState      :: ChainIndexState
        , _indexEvents     :: Seq (LogMessage ChainIndexEvent)
        , _indexFollowerID :: Maybe FollowerID
        } deriving (Eq, Show)

initialAppState :: AppState
initialAppState = AppState mempty mempty Nothing

newtype ChainIndexConfig =
    ChainIndexConfig
        { ciBaseUrl :: BaseUrl
        }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

makeLenses ''AppState
makeLenses ''ChainIndexConfig
