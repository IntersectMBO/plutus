{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Cardano.Protocol.Node where

import           Codec.Serialise.Class         (Serialise)
import           Data.Aeson                    (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy          as BSL
import           Data.List                     (findIndex)
import qualified Data.Map                      as Map
import           Data.Text.Prettyprint.Doc     (Pretty)
import           GHC.Generics

import           Control.Lens
import           Control.Monad.Freer.Extra.Log

import           Cardano.Prelude               (NoUnexpectedThunks)
import           Cardano.Slotting.Slot         (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block       (HeaderHash, Point (..), StandardHash)
import qualified Ouroboros.Network.Point       as Point

import           Ledger                        (Block, Slot (..), Tx (..), TxId (..), txId)
import qualified Ledger.Index                  as Index
import           LedgerBytes                   (LedgerBytes (..))
import           Plutus.SCB.EventLog

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

-- Node client
data ClientState = ClientState
  { _csChain       :: [Block]
  , _csIndex       :: Index.UtxoIndex
  , _csCurrentSlot :: Slot
  } deriving Show
makeLenses ''ClientState

emptyClientState :: ClientState
emptyClientState =  ClientState [] (Index.UtxoIndex Map.empty) (Slot 0)

type NodeClientEffects = '[EventLogEffect, Log]

getResumeOffset :: ClientState -> Point Block -> Maybe Integer
getResumeOffset (ClientState chain _ (Slot cntSlot))
                 (Point (At (Point.Block (SlotNo srvSlot) srvId)))
  = do
    let srvSlot' = toInteger srvSlot
    localIndex  <- toInteger <$> findIndex (srvId `sameHashAs`) chain
    if srvSlot' == cntSlot - localIndex
    then pure $ cntSlot - srvSlot'
    else Nothing
  where
    sameHashAs :: BlockId -> Block -> Bool
    sameHashAs srvId' block = srvId' == blockId block
-- NOTE: Something bad happened. We should send a local state reset event,
--       reset the local state and start a fresh download from the server.
getResumeOffset _ _ = error "Not yet implemented."

sampleLocalState :: ClientState -> [Point Block]
sampleLocalState cs =
    fmap mkPoint
  $ zip (SlotNo <$> [0 ..])
        (view csChain cs)
  where
    mkPoint :: (SlotNo, Block) -> Point Block
    mkPoint (slot, block) =
        Point (At (Point.Block slot $ blockId block))
