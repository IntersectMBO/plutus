module Chain.State (handleAction) where

import Chain.Types (Action(..), AnnotatedBlockchain, State, _chainFocus, _chainFocusAge, _findTx, _sequenceId)
import Clipboard (class MonadClipboard)
import Clipboard as Clipboard
import Control.Monad.State.Trans (class MonadState)
import Data.Lens (assign, preview, use)
import Data.Maybe (Maybe, fromMaybe)
import Plutus.V1.Ledger.TxId (TxId)
import Prelude (Ordering(..), Unit, bind, compare, discard, pure, ($), (<<<), (<>))
import Wallet.Rollup.Types (SequenceId(..))

handleAction :: forall m. MonadClipboard m => MonadState State m => Action -> Maybe AnnotatedBlockchain -> m Unit
handleAction (FocusTx newFocus) mAnnotatedBlockchain = do
  oldFocus <- use _chainFocus
  let
    relativeAge =
      fromMaybe EQ
        $ do
            annotatedBlockchain <- mAnnotatedBlockchain
            oldFocusTxId :: TxId <- oldFocus
            newFocusTxId :: TxId <- newFocus
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

handleAction (ClipboardAction subaction) _ = Clipboard.handleAction subaction
