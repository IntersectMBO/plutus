module InputField.State
  ( mkInitialState
  , handleAction
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Lens (assign, set)
import Data.Maybe (Maybe)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import InputField.Lenses (_pristine, _validator, _value)
import InputField.Types (Action(..), State)
import MainFrame.Types (ChildSlots, Msg)

mkInitialState :: forall e. Show e => String -> (String -> Maybe e) -> State e
mkInitialState value validator =
  { value
  , pristine: true
  , validator
  }

handleAction ::
  forall m e.
  MonadAff m =>
  MonadAsk Env m =>
  Show e =>
  Action e -> HalogenM (State e) (Action e) ChildSlots Msg m Unit
handleAction (SetValue value) =
  modify_
    $ set _value value
    <<< set _pristine false

handleAction (SetValidator validator) = assign _validator validator
