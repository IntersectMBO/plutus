module Rename.State where

import Prelude hiding (div)
import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (modalContent)
import Halogen.Css (classNames)
import Halogen.HTML (button, div, div_, input, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (class_, classes, value)
import MainFrame.Types (ChildSlots)
import Modal.ViewHelpers (modalHeader)
import Rename.Types (Action(..), State, _error, _projectName)

handleAction ::
  forall m.
  MonadAff m =>
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction (ChangeInput newName) = assign _projectName newName

handleAction SaveProject = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ modalHeader "Rename Project" Nothing
    , div [ classes [ modalContent ] ]
        [ input [ class_ (ClassName "project-name-input"), value (state ^. _projectName), onValueChange (Just <<< ChangeInput) ]
        , button
            [ onClick $ const $ Just SaveProject
            , classNames [ "btn" ]
            ]
            [ text "Save" ]
        , renderError (state ^. _error)
        ]
    ]
  where
  renderError Nothing = text ""

  renderError (Just err) = div [ class_ (ClassName "error") ] [ text err ]
