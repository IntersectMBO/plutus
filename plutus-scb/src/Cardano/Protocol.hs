{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS -fno-warn-orphans #-}

module Cardano.Protocol where

import           Codec.Serialise.Class           (Serialise)
import           Data.Aeson                      (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy            as BSL
import           Data.Functor                    (void)
import           Data.List                       (findIndex)
import           Data.Text.Prettyprint.Doc       (Pretty)
import           Eventful.Projection             (GlobalStreamProjection, Projection (..), StreamProjection (..))
import           Eventful.Store.Class
import           GHC.Generics

import           Control.Lens                    hiding (index, modifying, use)
import           Control.Monad.Freer             (Eff, Member, Members, type (~>), interpret, send)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State
import           Control.Monad.Freer.State       as Eff
import           Control.Monad.Freer.Writer

import           Cardano.Prelude                 (NoUnexpectedThunks)
import           Cardano.Slotting.Slot           (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block         (HeaderHash, Point (..), StandardHash, pointSlot)
import qualified Ouroboros.Network.Point         as Point

import           Ledger                          (Block, Slot (..), Tx (..), TxId (..), txId)
import qualified Ledger.Index                    as Index
import           LedgerBytes                     (LedgerBytes (..))
import           Plutus.SCB.EventLog
import           Plutus.SCB.Events
import           Plutus.SCB.Utils                (tshow)
import           Wallet.Emulator.Chain           (ChainEffect (..), ChainState (..), chainNewestFirst, currentSlot,
                                                  emptyChainState, handleChain, index, processBlock, queueTx)
import qualified Wallet.Emulator.Chain           as EM
import           Wallet.Emulator.NodeClient      (BlockValidated (..), NodeClientEffect (..), NodeClientEvent (..),
                                                  NodeClientState (..), handleNodeClient)

-- Block header
newtype BlockId = BlockId { getBlockId :: BSL.ByteString }
  deriving (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving newtype (Serialise, NoUnexpectedThunks)
  deriving (Pretty, Show) via LedgerBytes

blockId :: Block -> BlockId
blockId = BlockId . foldl BSL.append BSL.empty . map (getTxId . txId)

-- Making txs work with the node protocols
deriving instance StandardHash Tx
deriving instance StandardHash Block
deriving newtype instance NoUnexpectedThunks TxId
type instance HeaderHash Tx = TxId
type instance HeaderHash Block = BlockId

type ClientStreamProjection = GlobalStreamProjection ChainState ChainEvent

chainState :: Lens' ClientStreamProjection ChainState
chainState = lens getter setter where
    getter = streamProjectionState
    setter prj cs = prj { streamProjectionState = cs }

-- | The `Chain` effect should be interpreted in terms
-- of the `LogEvent` effect
type LoggedChainEffs = '[State EM.ChainState, Writer [EM.ChainEvent], EventLogEffect]

handleLoggedChain :: (Members LoggedChainEffs effs)
                  => Eff (ChainEffect ': effs) ~> Eff effs
handleLoggedChain = interpret $ \case
    ProcessBlock -> do -- Note: This is something that only the mock server can use.
        block <- handleChain processBlock
        appendEvent (NodeEvent $ BlockAdded block)
        pure block

    QueueTx tx -> do
        handleChain (queueTx tx)
        appendEvent (NodeEvent $ SubmittedTx tx)

-- | The `NodeClient` effect should be interpreted in terms
-- of the `LogEvent` effect
type LoggedNodeClientEffs = '[ChainEffect, State ChainState, State NodeClientState, Writer [NodeClientEvent], Writer [EM.ChainEvent], EventLogEffect, State ClientStreamProjection, Log]

handleLoggedNodeClient ::(Members LoggedNodeClientEffs effs)
                       => Eff (NodeClientEffect ': effs) ~> Eff effs
handleLoggedNodeClient = interpret $ \case
    ClientNotify (BlockValidated blk) -> do
        appendEvent (NodeEvent $ BlockAdded blk)
        get >>= updateProjection
    prg -> handleNodeClient (send prg)

-- | Client
resumeLocalState ::
    ( Member EventLogEffect effs
    , Member (State ClientStreamProjection) effs
    , Member Log effs
    )
 => Point Block
 -> Eff effs ChainState
resumeLocalState point = do
  cs <- use chainState
  getResumeOffset point >>= \case
    Nothing     -> error "Not yet implemented."
    Just 0      -> do
        logInfo "Resuming operation from last block received."
        return cs
    Just offset -> do
      let newChain = drop (fromIntegral offset) (cs ^. chainNewestFirst)
          newState =
            cs & set  chainNewestFirst newChain
               & set  index (Index.initialise newChain)
               & over currentSlot (\s -> s - Slot offset)
      logInfo $ "Resuming operation from " <> tshow offset <> " offset."
      appendEvent (NodeEvent $ Rollback (fromIntegral offset))
      return newState

getResumeOffset ::
    ( Member (State ClientStreamProjection) effs
    )
 => Point Block
 -> Eff effs (Maybe Integer)
getResumeOffset (Point (At (Point.Block (SlotNo srvSlot) srvId)))
  = do
    (ChainState chain _ _ (Slot cntSlot)) <- use chainState
    let srvSlot' = toInteger srvSlot
    pure $ do
      localIndex <- toInteger <$> findIndex (srvId `sameHashAs`) chain
      -- Check if the block we found has the same slot as the server.
      if srvSlot' == cntSlot - localIndex
      then pure $ cntSlot - srvSlot'
      else Nothing
  where
    sameHashAs :: BlockId -> Block -> Bool
    sameHashAs srvId' block = srvId' == blockId block
getResumeOffset _ = error "Not yet implemented."

getIntersectionPoints :: ChainState -> [Point Block]
getIntersectionPoints cs =
    fmap mkPoint
  $ zip (SlotNo <$> [0 ..])
        (view chainNewestFirst cs)
  where
    mkPoint :: (SlotNo, Block) -> Point Block
    mkPoint (slot, block) =
        Point (At (Point.Block slot $ blockId block))

-- Client state projections
updateChainState ::
    ( Member EventLogEffect effs
    , Member (State ClientStreamProjection) effs
    , Member Log effs
    )
 => Eff effs ()
updateChainState = do
  logInfo "Refresing event log chain state projection"
  prj :: ClientStreamProjection <- get
  updateProjection prj
  return ()

-- TODO: We should also update the tx pool .. maybe.
clientStateProjection :: Projection ChainState (VersionedStreamEvent ChainEvent)
clientStateProjection =
  Projection
    { projectionSeed = emptyChainState
    , projectionEventHandler = blockAddedHandler
    }
  where
    blockAddedHandler :: ChainState -> VersionedStreamEvent ChainEvent -> ChainState
    blockAddedHandler oldState
                      (StreamEvent _ _ (NodeEvent (BlockAdded block))) =
        over index (Index.insertBlock block)
      $ over chainNewestFirst (block :)
      $ over currentSlot (+1) oldState
    blockAddedHandler oldState _ = oldState

-- | Server

addBlock ::
  ( Member Log effs
  , Member ChainEffect effs )
 => Eff effs ()
addBlock = do
    logInfo "Adding new block to the chain."
    void processBlock

pointOffset :: Point Block
            -> Int
pointOffset pt =
  case pointSlot pt of
    Origin        -> 0
    At (SlotNo s) -> fromIntegral s

getChainPoints :: ChainState -> [Point Block]
getChainPoints st =
  zipWith mkPoint
    [(st ^. currentSlot) .. 0]
    (st ^. chainNewestFirst)
  where
    mkPoint :: Slot -> Block -> Point Block
    mkPoint (Slot s) block =
      Point (At (Point.Block (SlotNo $ fromIntegral s)
                          (blockId block)))
