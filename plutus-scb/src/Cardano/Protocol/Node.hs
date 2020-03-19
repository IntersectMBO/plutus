{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Node where

import           Codec.Serialise.Class           (Serialise)
import           Data.Aeson                      (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy            as BSL
import           Data.List                       (findIndex)
import qualified Data.Map                        as Map
import           Data.Text.Prettyprint.Doc       (Pretty)
import           GHC.Generics

import           Control.Lens                    hiding (use, modifying)
import           Control.Monad.Freer             (Eff, Member, raise, sendM)
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.Freer.Extra.State
import           Control.Monad.Freer.State       as Eff
import qualified Control.Monad.Freer.State       (State)

import           Cardano.Prelude                 (NoUnexpectedThunks)
import           Cardano.Slotting.Slot           (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block         (HeaderHash, Point (..), StandardHash)
import qualified Ouroboros.Network.Point         as Point

import           Ledger                          (Block, Slot (..), Tx (..), TxId (..), txId)
import qualified Ledger.Index                    as Index
import           LedgerBytes                     (LedgerBytes (..))
import           Plutus.SCB.EventLog
import           Plutus.SCB.Events
import           Plutus.SCB.Utils                (tshow)

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

data ClientState = ClientState
  { _csChain       :: [Block]
  , _csIndex       :: Index.UtxoIndex
  , _csCurrentSlot :: Slot
  , _csTxOutput    :: [Tx]
  } deriving Show
makeLenses ''ClientState

emptyClientState :: ClientState
emptyClientState =
  ClientState
    { _csChain = []
    , _csIndex = Index.UtxoIndex Map.empty
    , _csCurrentSlot = Slot 0
    , _csTxOutput = []
    }

type NodeClientEffects m = '[EventLogEffect, State ClientState, Log, m]

-- Send transaction.
sendTx ::
    ( Member EventLogEffect effs
    , Member (State ClientState) effs
    , Member Log effs
    )
 => Tx
 -> Eff effs ()
sendTx tx = do
    appendEvent (NodeEvent $ SubmittedTx tx)
    modifying csTxOutput (tx :)

-- Chain sync client

-- Publish newly received block to the event stream.
publishNewBlock ::
    ( Member EventLogEffect effs
    , Member (State ClientState) effs
    , Member Log effs
    )
 => Block
 -> Eff effs ()
publishNewBlock block = do
    chain <- use csChain
    logInfo "Received new block."
    appendEvents
      [ NodeEvent $ BlockAdded block
      , NodeEvent $ NewSlot (fromIntegral $ length chain) []
      ]

-- Resume from an event log.
resumeLocalState ::
    ( Member EventLogEffect effs
    , Member (State ClientState) effs
    , Member Log effs
    )
 => Point Block
 -> Eff effs ClientState
resumeLocalState point = do
  cs <- get
  getResumeOffset point >>= \case
    Nothing     -> error "Not yet implemented."
    Just 0      -> do
        logInfo "Resuming operation from last block received."
        return cs
    Just offset -> do
      let newChain = drop (fromIntegral offset) (cs ^. csChain)
          newState =
            cs & set  csChain newChain
               & set  csIndex (Index.initialise newChain)
               & over csCurrentSlot (\s -> s - Slot offset)
      logInfo $ "Resuming operation from " <> tshow offset <> " offset."
      appendEvent (NodeEvent $ Rollback (fromIntegral offset))
      return newState

getResumeOffset ::
    ( Member (State ClientState) effs
    , Member Log effs
    )
 => Point Block
 -> Eff effs (Maybe Integer)
getResumeOffset {-(ClientState chain _ (Slot cntSlot))-}
                (Point (At (Point.Block (SlotNo srvSlot) srvId)))
  = do
    (ClientState chain _ (Slot cntSlot) _) <- get
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

wrapLocalState :: ClientState -> [Point Block]
wrapLocalState cs =
    fmap mkPoint
  $ zip (SlotNo <$> [0 ..])
        (view csChain cs)
  where
    mkPoint :: (SlotNo, Block) -> Point Block
    mkPoint (slot, block) =
        Point (At (Point.Block slot $ blockId block))

-- State projections
