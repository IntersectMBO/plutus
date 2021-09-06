module Plutus.ChainIndex.Compatibility where

import           Cardano.Api                (BlockHeader, BlockInMode (..), BlockNo (..), CardanoMode, ChainTip (..),
                                             Hash, SlotNo (..), serialiseToRawBytes)
import           Ledger                     (BlockId (..), Slot (..))
import           Plutus.ChainIndex.Tx       (ChainIndexTx (..), fromOnChainTx)
import           Plutus.ChainIndex.Types    (Tip (..))
import qualified Plutus.Contract.CardanoAPI as C

fromCardanoTip :: ChainTip -> Tip
fromCardanoTip (ChainTip slotNo hash blockNo) =
    Tip { tipSlot = fromCardanoSlot slotNo
        , tipBlockId = fromCardanoBlockId hash
        , tipBlockNo = fromCardanoBlockNo blockNo
        }
fromCardanoTip ChainTipAtGenesis = TipAtGenesis

fromCardanoSlot :: SlotNo -> Slot
fromCardanoSlot (SlotNo slotNo) = Slot $ toInteger slotNo

fromCardanoBlockId :: Hash BlockHeader -> BlockId
fromCardanoBlockId hash =
    BlockId $ serialiseToRawBytes hash

fromCardanoBlockNo :: BlockNo -> Int
fromCardanoBlockNo (BlockNo blockNo) =
    fromInteger $ toInteger blockNo

fromCardanoBlock
    :: BlockInMode CardanoMode
    -> Either C.FromCardanoError [ChainIndexTx]
fromCardanoBlock cBlock =
    (fmap . fmap) fromOnChainTx $ C.fromCardanoBlock cBlock
