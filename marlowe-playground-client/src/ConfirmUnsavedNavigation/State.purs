module ConfirmUnsavedNavigation.State where

import Halogen.HTML
import ConfirmUnsavedNavigation.Types (Action(..), State, _wantsToSaveProject)
import Data.Lens (assign)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class.Console (log)
import Halogen (HalogenM, liftEffect)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Prelude (Unit, Void, const, ($), discard)
import Servant.PureScript.Settings (SPSettings_)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings DontSaveProject = do
  liftEffect $ log $ "setting wants to save to false"
  assign _wantsToSaveProject false

handleAction settings _ = do
  liftEffect $ log $ "setting wants to save to true"
  assign _wantsToSaveProject true

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ ClassName "modal-content" ] ]
    [ p_ [ text "Clicking on the Marlowe logo will take you out of the editor and return you to the home page." ]
    , p_ [ text "Unsaved changes will be lost." ]
    , p_ [ text "Do you want to save changes to 'Untitled'?" ]
    , button [ onClick $ const $ Just Cancel ] [ text "Cancel" ]
    , button [ onClick $ const $ Just DontSaveProject ] [ text "Don't Save" ]
    , button [ onClick $ const $ Just SaveProject ] [ text "Save" ]
    ]
