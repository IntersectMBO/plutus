module NewProject.State where

import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (fontSemibold, modalContent, newProjectBlocklyIcon, newProjectHaskellIcon, newProjectJavascriptIcon, newProjectMarloweIcon, textBase, textSm)
import Halogen.HTML (div, div_, h3, img, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, src)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Modal.ViewHelpers (modalHeaderTitle)
import NewProject.Types (Action(..), State, _error)
import Prelude (Unit, Void, const, map, pure, unit, ($), (<<<))
import Projects.Types (Lang(..))
import Servant.PureScript.Settings (SPSettings_)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings (CreateProject lang) = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ modalHeaderTitle "New Project"
    , div [ classes [ modalContent, ClassName "new-project-container" ] ]
        [ h3 [ classes [ textBase, fontSemibold ] ] [ text "Please choose your initial coding environment" ]
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
      , span [ classes [ textSm, fontSemibold ] ]
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
