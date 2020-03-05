{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Cardano.ChainIndex.Types where

import           Control.Lens               (makeLenses)
import           Data.Sequence              (Seq)
import           Servant.Client             (BaseUrl)

import           Wallet.Emulator.ChainIndex (ChainIndexEvent, ChainIndexState)

data AppState =
    AppState
        { _indexState  :: ChainIndexState
        , _indexEvents :: Seq ChainIndexEvent
        }

initialAppState :: AppState
initialAppState = AppState mempty mempty

newtype ChainIndexConfig =
    ChainIndexConfig
        { ciBaseUrl :: BaseUrl
        }

makeLenses ''AppState
makeLenses ''ChainIndexConfig
