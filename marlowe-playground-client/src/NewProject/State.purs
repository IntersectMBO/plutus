module NewProject.State where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (newProjectHaskellIcon, newProjectJavascriptIcon, newProjectMarloweIcon, newProjectBlocklyIcon)
import Halogen.HTML (button, div, h2_, hr_, input, text, img)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (class_, classes, value, src)
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
  div [ classes [ ClassName "new-project-container" ] ]
    [ input [ value (state ^. _projectName), onValueChange (Just <<< ChangeProjectName) ]
    , hr_
    , h2_ [ text "Please choose your initial coding environment" ]
    , div [ classes [ ClassName "environment-selector-group" ] ] (map link [ Haskell, Javascript, Marlowe, Blockly ])
    , renderError (state ^. _error)
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
      , text $ langTitle lang
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
