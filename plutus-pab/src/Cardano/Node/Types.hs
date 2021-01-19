{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}

module Cardano.Node.Types where

import           Control.Lens                   (Iso', iso, makeLenses, view)
import           Control.Monad.Freer.Log        (LogMessage)
import           Data.Aeson                     (FromJSON, ToJSON)
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           Data.Text.Prettyprint.Doc      (Pretty)
import           Data.Time.Units                (Second)
import           Data.Time.Units.Extra          ()
import           GHC.Generics                   (Generic)
import qualified Language.Plutus.Contract.Trace as Trace
import           Servant                        (FromHttpApiData, ToHttpApiData)
import           Servant.Client                 (BaseUrl)
import           Wallet.Emulator                (Wallet)
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
        , mscInitialTxWallets :: [Wallet]
        -- ^ The wallets that receive money from the initial transaction.
        , mscSocketPath       :: FilePath
        -- ^ Path to the socket used to communicate with the server.
        }
    deriving (Show, Eq, Generic, FromJSON)

data AppState =
    AppState
        { _chainState    :: ChainState
        , _eventHistory  :: [LogMessage ChainEvent]
        , _followerState :: NodeFollowerState
        }
    deriving (Show)


initialChainState :: Trace.InitialDistribution -> ChainState
initialChainState =
    view EM.chainState .
    MultiAgent.emulatorStateInitialDist . Map.mapKeys EM.walletPubKey

-- | 'AppState' with an initial transaction that pays some Ada to
--   the wallets.
initialAppState :: [Wallet] -> AppState
initialAppState wallets =
    AppState
        { _chainState = initialChainState (Trace.defaultDistFor wallets)
        , _eventHistory = mempty
        , _followerState = initialFollowerState
        }

newtype NodeFollowerState = NodeFollowerState { _unNodeFollowerState :: Map FollowerID Int }
    deriving (Show)

_NodeFollowerState :: Iso' NodeFollowerState (Map FollowerID Int)
_NodeFollowerState = iso _unNodeFollowerState NodeFollowerState

initialFollowerState :: NodeFollowerState
initialFollowerState = NodeFollowerState Map.empty

newtype FollowerID = FollowerID Int
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (ToJSON, FromJSON, ToHttpApiData, FromHttpApiData, Integral, Enum, Real, Num, Pretty)

makeLenses 'AppState
