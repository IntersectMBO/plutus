module Chain.Eval (eval) where

import Chain.Types (AnnotatedBlockchain, ChainFocus, State, TxId, _FocusTx, _chainFocus, _chainFocusAge, _chainFocusAppearing, _findTx, _sequenceId)
import Control.Monad.State.Trans (class MonadState)
import Data.Lens (_Just, assign, preview, use)
import Data.Maybe (Maybe, fromMaybe)
import Data.Newtype (wrap)
import MonadApp (class MonadApp, delay)
import Playground.Types (SequenceId(..))
import Prelude (Ordering(..), bind, compare, discard, pure, ($), (<<<), (<>))

eval :: forall m a. MonadState State m => MonadApp m => Maybe ChainFocus -> Maybe AnnotatedBlockchain -> a -> m a
eval newFocus mAnnotatedBlockchain next = do
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
  -- Animate.
  assign _chainFocusAppearing true
  delay $ wrap 10.0
  assign _chainFocusAppearing false

  pure next
  where
  compareSequenceIds (SequenceId old) (SequenceId new) =
    compare old.slotIndex new.slotIndex
      <> compare old.txIndex new.txIndex
