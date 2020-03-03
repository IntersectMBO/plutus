{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Cardano.Node.Types where

import           Control.Lens                   (makeLenses, view)
import           Data.Aeson                     (FromJSON)
import qualified Data.Map                       as Map
import           Data.Time.Units                (Second)
import           Data.Time.Units.Extra          ()
import           GHC.Generics                   (Generic)
import qualified Language.Plutus.Contract.Trace as Trace
import           Servant.Client                 (BaseUrl)
import qualified Wallet.Emulator                as EM
import           Wallet.Emulator.Chain          (ChainEvent, ChainState)
import qualified Wallet.Emulator.MultiAgent     as MultiAgent

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

initialChainState :: Trace.InitialDistribution -> ChainState
initialChainState =
    view EM.chainState .
    MultiAgent.emulatorStateInitialDist . Map.mapKeys EM.walletPubKey

initialAppState :: AppState
initialAppState =
    AppState
        { _chainState = initialChainState Trace.defaultDist
        , _eventHistory = mempty
        }
