{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Cardano.Streaming.Helpers where

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as CS
import Cardano.Chain.Genesis qualified
import Cardano.Crypto (ProtocolMagicId (unProtocolMagicId),
                       RequiresNetworkMagic (RequiresMagic, RequiresNoMagic))
import Cardano.Ledger.Shelley.LedgerState qualified as SL
import Cardano.Slotting.Slot (WithOrigin (At, Origin))
import Control.Concurrent.Async qualified as IO
import Control.Exception qualified as IO
import Data.SOP.Strict (NP ((:*)))
import GHC.Generics (Generic)
import Ouroboros.Consensus.Cardano.CanHardFork qualified as Consensus
import Ouroboros.Consensus.HardFork.Combinator qualified as Consensus
import Ouroboros.Consensus.HardFork.Combinator.AcrossEras qualified as HFC
import Ouroboros.Consensus.HardFork.Combinator.Basics qualified as HFC
import Ouroboros.Consensus.Shelley.Ledger qualified as O
import Streaming.Prelude qualified as S

-- * ChainSyncEvent

data ChainSyncEvent a
  = RollForward a C.ChainTip
  | RollBackward C.ChainPoint C.ChainTip
  deriving (Show, Functor, Generic)

data ChainSyncEventException
  = NoIntersectionFound
  deriving (Show)

instance IO.Exception ChainSyncEventException

data RollbackException = RollbackLocationNotFound C.ChainPoint C.ChainTip
  deriving (Eq, Show)
instance IO.Exception RollbackException

-- * Orphans

instance IO.Exception C.FoldBlocksError

-- * Block

bimBlockNo :: C.BlockInMode -> C.BlockNo
bimBlockNo (C.BlockInMode _era (C.Block (C.BlockHeader _ _ blockNo) _)) = blockNo

bimSlotNo :: C.BlockInMode -> C.SlotNo
bimSlotNo (C.BlockInMode _era (C.Block (C.BlockHeader slotNo _ _) _)) = slotNo

getEpochNo :: C.LedgerState -> Maybe CS.EpochNo
getEpochNo = \case
  C.LedgerStateByron _st -> Nothing
  C.LedgerStateShelley st -> fromState st
  C.LedgerStateAllegra st -> fromState st
  C.LedgerStateMary st -> fromState st
  C.LedgerStateAlonzo st -> fromState st
  C.LedgerStateBabbage st -> fromState st
  C.LedgerStateConway st -> fromState st
 where
  fromState = Just . SL.nesEL . O.shelleyLedgerState

fromChainTip :: C.ChainTip -> WithOrigin C.BlockNo
fromChainTip ct = case ct of
  C.ChainTipAtGenesis -> Origin
  C.ChainTip _ _ bno  -> At bno

-- * IO

linkedAsync :: IO a -> IO ()
linkedAsync action = IO.link =<< IO.async action

-- * LocalNodeConnectInfo

mkLocalNodeConnectInfo :: C.NetworkId -> C.SocketPath -> C.LocalNodeConnectInfo
mkLocalNodeConnectInfo networkId socketPath =
  C.LocalNodeConnectInfo
    { C.localConsensusModeParams = C.CardanoModeParams epochSlots
    , C.localNodeNetworkId = networkId
    , C.localNodeSocketPath = socketPath
    }
 where
  -- This a parameter needed only for the Byron era. Since the Byron
  -- era is over and the parameter has never changed it is ok to
  -- hardcode this. See comment on `Cardano.Api.ConsensusModeParams` in
  -- cardano-node.
  epochSlots = C.EpochSlots 21600 -- TODO: is this configurable? see below

-- | Derive LocalNodeConnectInfo from Env.
mkConnectInfo :: C.Env -> C.SocketPath -> C.LocalNodeConnectInfo
mkConnectInfo env socketPath =
  C.LocalNodeConnectInfo
    { C.localConsensusModeParams = cardanoModeParams
    , C.localNodeNetworkId = networkId'
    , C.localNodeSocketPath = socketPath
    }
 where
  -- Derive the NetworkId as described in network-magic.md from the
  -- cardano-ledger-specs repo.
  byronConfig =
    (\(Consensus.WrapPartialLedgerConfig (Consensus.ByronPartialLedgerConfig bc _) :* _) -> bc)
      . HFC.getPerEraLedgerConfig
      . HFC.hardForkLedgerConfigPerEra
      $ C.envLedgerConfig env

  networkMagic =
    C.NetworkMagic $
      unProtocolMagicId $
        Cardano.Chain.Genesis.gdProtocolMagicId $
          Cardano.Chain.Genesis.configGenesisData byronConfig

  networkId' = case Cardano.Chain.Genesis.configReqNetMagic byronConfig of
    RequiresNoMagic -> C.Mainnet
    RequiresMagic   -> C.Testnet networkMagic

  cardanoModeParams = C.CardanoModeParams . C.EpochSlots $ 10 * C.envSecurityParam env

{- | Ignore rollback events in the chainsync event stream. Useful for
monitor which blocks has been seen by the node, regardless whether
they are permanent.
-}
ignoreRollbacks :: (Monad m) => S.Stream (S.Of (ChainSyncEvent a)) m r -> S.Stream (S.Of a) m r
ignoreRollbacks = S.mapMaybe (\case RollForward e _ -> Just e; _ -> Nothing)
