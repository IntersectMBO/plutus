{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes       #-}

module Cardano.Protocol.Node where

import           Codec.Serialise.Class           (Serialise)
import           Data.Aeson                      (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy            as BSL
import           Data.List                       (findIndex)
import           Data.Text.Prettyprint.Doc       (Pretty)
import           Eventful.Projection             (GlobalStreamProjection, Projection (..), StreamProjection (..))
import           Eventful.Store.Class
import           GHC.Generics

import           Control.Lens                    hiding (index, modifying, use)
import           Control.Monad.Freer             (Eff, LastMember, Member, Members, type (~>), interpret)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State
import           Control.Monad.Freer.State       as Eff
import           Control.Monad.Freer.Writer

import           Cardano.Prelude                 (NoUnexpectedThunks)
import           Cardano.Slotting.Slot           (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block         (HeaderHash, Point (..), StandardHash)
import qualified Ouroboros.Network.Point         as Point

import           Ledger                          (Block, Slot (..), Tx (..), TxId (..), txId)
import qualified Ledger.AddressMap               as AM
import qualified Ledger.Index                    as Index
import           LedgerBytes                     (LedgerBytes (..))
import           Plutus.SCB.Core                 (MonadEventStore)
import           Plutus.SCB.EventLog
import qualified Plutus.SCB.Events               as Evt
import           Plutus.SCB.Utils                (tshow)
import           Wallet.Emulator.Chain           (ChainEffect (..), ChainEvent (..), ChainState (..),
                                                  ValidatedBlock (..), chainNewestFirst, currentSlot, emptyChainState,
                                                  index, txPool, validateBlock, queueTx)
import           Wallet.Emulator.NodeClient      (NodeClientEffect (..), Notification (..), NodeClientEvent(..))

-- Block header
newtype BlockId = BlockId { getBlockId :: BSL.ByteString }
  deriving (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving newtype (Serialise, NoUnexpectedThunks)
  deriving (Pretty, Show) via LedgerBytes

blockId :: Block -> BlockId
blockId = BlockId . foldl BSL.append BSL.empty . map (getTxId . txId)

-- Making Tx work with the node protocols
type instance HeaderHash Tx = TxId
type instance HeaderHash Block = BlockId
deriving instance StandardHash Tx

deriving instance StandardHash Block
deriving newtype instance NoUnexpectedThunks TxId

type ClientStreamProjection = GlobalStreamProjection ChainState Evt.ChainEvent

chainState :: Lens' ClientStreamProjection ChainState
chainState = lens getter setter where
    getter = streamProjectionState
    setter prj cs = prj { streamProjectionState = cs }

type NodeClientEffects m = '[ChainEffect, State ChainState, Writer [NodeClientEvent], Writer [ChainEvent], EventLogEffect, State ClientStreamProjection, Log, m]

-- Make handleChain use the EventLog.
type ChainEffs m = '[State ChainState, Writer [ChainEvent], EventLogEffect, m]

-- Note: This is how I would modify the following handlers
--       to add event log effects
handleChain' ::
    ( Members (ChainEffs m) effs
    , LastMember m effs
    , MonadEventStore Evt.ChainEvent m )
 => Eff (ChainEffect ': effs) ~> Eff effs
handleChain' = interpret $ \case
    ProcessBlock -> do -- Note: This is something that only the mock server can use.
        st <- get
        let pool  = st ^. txPool
            slot  = st ^. currentSlot
            idx   = st ^. index
            (ValidatedBlock block events rest, idx') =
                validateBlock slot idx pool

        let st' = st & txPool .~ rest
                   & chainNewestFirst %~ (block :)
                   & index .~ idx'
                   & currentSlot +~ 1 -- This assumes that there is exactly one block per slot. In the real chain there may be more than one block per slot.
        put st'
        tell events
        appendEvents
          [ Evt.NodeEvent $ Evt.BlockAdded block
          , Evt.NodeEvent $ Evt.NewSlot (fromIntegral $ st' ^. currentSlot) []
          ]

        pure block
    QueueTx tx -> do
        modify $ over txPool (tx :)
        appendEvent (Evt.NodeEvent $ Evt.SubmittedTx tx)

handleNodeClient' ::
    ( Members (NodeClientEffects m) effs
    , LastMember m effs
    , MonadEventStore Evt.ChainEvent m
    )
 => Eff (NodeClientEffect ': effs) ~> Eff effs
handleNodeClient' = interpret $ \case
    PublishTx tx   -> queueTx tx >> tell [TxSubmit (txId tx)]
    GetClientSlot  -> use $ chainState . currentSlot
    GetClientIndex -> error "Handled by the ChainIndex effect."\
    -- Note: I am using this to log the newly received block to the event stream.
    --       I would do away with the Notification and remove CurrentSlot which is
    --       not used anywhere.
    ClientNotify n -> case n of
        BlockValidated blk -> do
            appendEvent (Evt.NodeEvent $ Evt.BlockAdded blk)
            get >>= updateProjection

        CurrentSlot sl -> do   -- this is not really needed.
            appendEvent (Evt.NodeEvent $ Evt.NewSlot sl [])
            get >>= updateProjection

-- Chain sync client

-- Resume from an event log.
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
      appendEvent (Evt.NodeEvent $ Evt.Rollback (fromIntegral offset))
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

wrapLocalState :: ChainState -> [Point Block]
wrapLocalState cs =
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
clientStateProjection :: Projection ChainState (VersionedStreamEvent Evt.ChainEvent)
clientStateProjection =
  Projection
    { projectionSeed = emptyChainState
    , projectionEventHandler = blockAddedHandler
    }
  where
    blockAddedHandler :: ChainState -> VersionedStreamEvent Evt.ChainEvent -> ChainState
    blockAddedHandler oldState
                      (StreamEvent _ _ (Evt.NodeEvent (Evt.BlockAdded block))) =
        over index (Index.insertBlock block)
      $ over chainNewestFirst (block :)
      $ over currentSlot (+1) oldState
    blockAddedHandler oldState _ = oldState
