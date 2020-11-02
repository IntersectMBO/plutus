module Rename.State where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.HTML (button, div, input, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (class_, classes, value)
import Marlowe (SPParams_)
import Prelude (Unit, Void, const, pure, unit, ($), (<<<))
import Rename.Types (Action(..), State, _error, _projectName)
import Servant.PureScript.Settings (SPSettings_)
import MainFrame.Types (ChildSlots)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings (ChangeInput newName) = assign _projectName newName

handleAction settings SaveProject = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ ClassName "new-project-container" ] ]
    [ input [ value (state ^. _projectName), onValueChange (Just <<< ChangeInput) ]
    , button [ onClick $ const $ Just SaveProject ] [ text "Save" ]
    , renderError (state ^. _error)
    ]
  where
  renderError Nothing = text ""

  renderError (Just err) = div [ class_ (ClassName "error") ] [ text err ]
