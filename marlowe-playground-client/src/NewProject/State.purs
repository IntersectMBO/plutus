module NewProject.State where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (newProjectHaskellIcon, newProjectJavascriptIcon, newProjectMarloweIcon, newProjectBlocklyIcon)
import Halogen.HTML (button, div, div_, h2, h2_, h3, hr_, img, input, span, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (class_, classes, src, value)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import NewProject.Types (Action(..), State, _error, _projectName)
import Prelude (Unit, Void, const, map, pure, show, unit, ($), (<<<))
import Projects.Types (Lang(..))
import Servant.PureScript.Settings (SPSettings_)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings (ChangeProjectName newName) = assign _projectName newName

handleAction settings (CreateProject lang) = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ div [ classes [ ClassName "modal-header" ] ]
        [ {-
            TODO: confirm that we dont want to change the project name and remove
            input [ value (state ^. _projectName), onValueChange (Just <<< ChangeProjectName) ]
             TODO: create an HTML helper so all dialogs have the same header/title?
          -} h2 [ classes [ ClassName "title" ] ] [ text "New Project" ]
        ]
    , div [ classes [ ClassName "modal-content", ClassName "new-project-container" ] ]
        [ h3 [ classes [ ClassName "text-base", ClassName "font-semibold" ] ] [ text "Please choose your initial coding environment" ]
        , div [ classes [ ClassName "environment-selector-group" ] ] (map link [ Haskell, Javascript, Marlowe, Blockly ])
        , renderError (state ^. _error)
        ]
    ]
  where
  renderError Nothing = text ""

  renderError (Just err) = div [ class_ (ClassName "error") ] [ text err ]

  link lang =
    div
      [ classes [ ClassName "environment-selector" ]
      , onClick (const <<< Just $ CreateProject lang)
      ]
      [ img [ src $ langIcon lang ]
      , span [ classes [ ClassName "font-semibold", ClassName "text-sm" ] ]
          [ text $ langTitle lang ]
      ]

  langIcon = case _ of
    Haskell -> newProjectHaskellIcon
    Javascript -> newProjectJavascriptIcon
    Marlowe -> newProjectMarloweIcon
    Blockly -> newProjectBlocklyIcon
    _ -> "" -- The default should never happen but it's not checked at the type level

  langTitle = case _ of
    Haskell -> "Haskell Editor"
    Javascript -> "JS Editor"
    Marlowe -> "Marlowe"
    Blockly -> "Blockly"
    _ -> ""
