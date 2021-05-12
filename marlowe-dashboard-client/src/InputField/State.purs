module InputField.State
  ( dummyState
  , initialState
  , handleAction
  , validate
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Lens (assign, set, view)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import InputField.Lenses (_pristine, _validator, _value)
import InputField.Types (class InputFieldError, Action(..), State)

-- see note [dummyState] in MainFrame.State
dummyState :: forall e. InputFieldError e => State e
dummyState = initialState

initialState :: forall e. InputFieldError e => State e
initialState =
  { value: mempty
  , pristine: true
  , validator: const Nothing
  }

handleAction ::
  forall m e slots msg.
  MonadAff m =>
  MonadAsk Env m =>
  InputFieldError e =>
  Action e -> HalogenM (State e) (Action e) slots msg m Unit
handleAction (SetValue value) =
  modify_
    $ set _value value
    <<< set _pristine false

handleAction (SetValidator validator) = assign _validator validator

handleAction Reset =
  modify_
    $ set _value mempty
    <<< set _pristine true
    <<< set _validator (const Nothing)

validate :: forall e. InputFieldError e => State e -> Maybe e
validate state =
  let
    value = view _value state

    validator = view _validator state
  in
    validator value
