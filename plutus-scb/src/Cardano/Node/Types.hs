{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Cardano.Node.Types where

import           Control.Lens          (makeLenses)
import           Data.Aeson            (FromJSON)
import           Data.Time.Units       (Second)
import           Data.Time.Units.Extra ()
import           GHC.Generics          (Generic)
import           Servant.Client        (BaseUrl)
import           Wallet.Emulator.Chain (ChainEvent, ChainState)

data BlockReaperConfig =
    BlockReaperConfig
        { brcInterval     :: Second
        , brcBlocksToKeep :: Int
        }
    deriving (Show, Eq, Generic, FromJSON)

data MockServerConfig =
    MockServerConfig
        { mscBaseUrl          :: BaseUrl
        , mscSlotLength       :: Second
        -- ^ Duration of one slot
        , mscRandomTxInterval :: Maybe Second
        -- ^ Time between two randomly generated transactions
        , mscBlockReaper      :: Maybe BlockReaperConfig
        -- ^ When to discard old blocks
        }
    deriving (Show, Eq, Generic, FromJSON)

data AppState =
    AppState
        { _chainState   :: ChainState
        , _eventHistory :: [ChainEvent]
        }
    deriving (Show)

makeLenses 'AppState
