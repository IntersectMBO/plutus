module Chain.Eval (handleAction) where

import Chain.Types (AnnotatedBlockchain, ChainFocus, State, _FocusTx, _chainFocus, _chainFocusAge, _findTx, _sequenceId)
import Control.Monad.State.Trans (class MonadState)
import Data.Lens (_Just, assign, preview, use)
import Data.Maybe (Maybe, fromMaybe)
import Ledger.TxId (TxId)
import Prelude (Ordering(..), Unit, bind, compare, discard, pure, ($), (<<<), (<>))
import Wallet.Rollup.Types (SequenceId(..))

handleAction :: forall m. MonadState State m => Maybe ChainFocus -> Maybe AnnotatedBlockchain -> m Unit
handleAction newFocus mAnnotatedBlockchain = do
  oldFocus <- use _chainFocus
  let
    relativeAge =
      fromMaybe EQ
        $ do
            annotatedBlockchain <- mAnnotatedBlockchain
            oldFocusTxId :: TxId <- preview (_Just <<< _FocusTx) oldFocus
            newFocusTxId :: TxId <- preview (_Just <<< _FocusTx) newFocus
            oldFocusSequenceId :: SequenceId <- preview (_findTx oldFocusTxId <<< _sequenceId) annotatedBlockchain
            newFocusSequenceId :: SequenceId <- preview (_findTx newFocusTxId <<< _sequenceId) annotatedBlockchain
            pure $ compareSequenceIds oldFocusSequenceId newFocusSequenceId
  -- Update.
  assign _chainFocus newFocus
  assign _chainFocusAge relativeAge
  where
  compareSequenceIds (SequenceId old) (SequenceId new) =
    compare old.slotIndex new.slotIndex
      <> compare old.txIndex new.txIndex
