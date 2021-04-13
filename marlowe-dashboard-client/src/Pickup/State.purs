module Pickup.State
  ( initialState
  , handleAction
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Lens (assign)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM)
import MainFrame.Lenses (_card, _pickupState)
import MainFrame.Types (ChildSlots, Msg)
import MainFrame.Types (Action, State) as MainFrame
import Pickup.Types (Action(..), State)

initialState :: State
initialState =
  { card: Nothing
  , pickupWalletString: mempty
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State].
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM MainFrame.State MainFrame.Action ChildSlots Msg m Unit
handleAction (SetCard card) = assign (_pickupState <<< _card) card

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit
