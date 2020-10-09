module NewProject where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (flex)
import Halogen.HTML (a, div, h2_, hr_, input, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (class_, classes, value)
import Marlowe (SPParams_)
import NewProject.Types (Action(..), State, _error, _projectName)
import Prelude (Unit, Void, const, map, pure, show, unit, ($), (<<<))
import Projects.Types (Lang(..))
import Servant.PureScript.Settings (SPSettings_)
import Types (ChildSlots)

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
    , h2_ [ text "Choose your initial coding environment" ]
    , div [ classes [ flex, ClassName "language-links" ] ] (map link [ Haskell, Marlowe, Blockly ])
    , renderError (state ^. _error)
    ]
  where
  renderError Nothing = text ""

  renderError (Just err) = div [ class_ (ClassName "error") ] [ text err ]

  link lang = a [ onClick (const <<< Just $ CreateProject lang) ] [ text $ show lang ]
