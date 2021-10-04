module Plutus.ChainIndex.Compatibility where

import           Cardano.Api                (Block (..), BlockHeader (..), BlockInMode (..), BlockNo (..), CardanoMode,
                                             ChainPoint (..), ChainTip (..), Hash, SlotNo (..), serialiseToRawBytes)
import           Ledger                     (BlockId (..), Slot (..))
import           Plutus.ChainIndex.Tx       (ChainIndexTx (..))
import           Plutus.ChainIndex.Types    (BlockNumber (..), Point (..), Tip (..))
import qualified Plutus.Contract.CardanoAPI as C

fromCardanoTip :: ChainTip -> Tip
fromCardanoTip (ChainTip slotNo hash blockNo) =
    Tip { tipSlot = fromCardanoSlot slotNo
        , tipBlockId = fromCardanoBlockId hash
        , tipBlockNo = fromCardanoBlockNo blockNo
        }
fromCardanoTip ChainTipAtGenesis = TipAtGenesis

fromCardanoPoint :: ChainPoint -> Point
fromCardanoPoint ChainPointAtGenesis = PointAtGenesis
fromCardanoPoint (ChainPoint slot hash) =
    Point { pointSlot = fromCardanoSlot slot
          , pointBlockId = fromCardanoBlockId hash
          }

tipFromCardanoBlock
  :: BlockInMode CardanoMode
  -> Tip
tipFromCardanoBlock (BlockInMode (Block (BlockHeader slot hash block) _) _) =
    fromCardanoTip $ ChainTip slot hash block

fromCardanoSlot :: SlotNo -> Slot
fromCardanoSlot (SlotNo slotNo) = Slot $ toInteger slotNo

fromCardanoBlockId :: Hash BlockHeader -> BlockId
fromCardanoBlockId hash =
    BlockId $ serialiseToRawBytes hash

fromCardanoBlockHeader :: BlockHeader -> Tip
fromCardanoBlockHeader (BlockHeader slotNo hash blockNo) =
    Tip { tipSlot = fromCardanoSlot slotNo
        , tipBlockId = fromCardanoBlockId hash
        , tipBlockNo = fromCardanoBlockNo blockNo
        }

fromCardanoBlockNo :: BlockNo -> BlockNumber
fromCardanoBlockNo (BlockNo blockNo) = BlockNumber blockNo

fromCardanoBlock
    :: BlockInMode CardanoMode
    -> Either C.FromCardanoError [ChainIndexTx]
fromCardanoBlock = C.fromCardanoBlock
