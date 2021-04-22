module Pickup.State
  ( dummyState
  , initialState
  , handleAction
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Lens (assign)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM)
import MainFrame.Lenses (_card)
import MainFrame.Types (ChildSlots, Msg)
import Pickup.Types (Action(..), State)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = initialState

initialState :: State
initialState =
  { card: Nothing
  , pickupWalletString: mempty
  , pickingUp: false
  }

-- Some actions are handled in `MainFrame.State` because they involve
-- modifications of that state. See Note [State] in MainFrame.State.
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (SetCard card) = assign _card card

-- all other actions are handled in `MainFrame.State`
handleAction _ = pure unit
