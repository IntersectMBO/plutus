module SaveAs.State where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (activeBorderBlue700, border, borderBlue300, btn, btnSecondary, fontSemibold, fullWidth, modalContent, noMargins, spaceBottom, spaceLeft, spaceRight, spaceTop, textBase, textRight, textSm, uppercase)
import Halogen.HTML (button, div, div_, h2, input, text)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, placeholder, value)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Prelude (Unit, Void, const, pure, unit, ($), (<<<), (==))
import SaveAs.Types (Action(..), State, _error, _projectName)
import Servant.PureScript.Settings (SPSettings_)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings (ChangeInput newName) = assign _projectName newName

handleAction settings _ = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ div [ classes [ spaceTop, spaceLeft ] ]
        [ h2 [ classes [ textBase, fontSemibold, noMargins ] ] [ text "Save as" ]
        ]
    , div [ classes [ modalContent, ClassName "saved-as-modal" ] ]
        [ input
            [ classes [ spaceBottom, fullWidth, textSm, border, borderBlue300, activeBorderBlue700 ]
            , value (state ^. _projectName)
            , onValueInput (Just <<< ChangeInput)
            , placeholder "Type a name for your project"
            ]
        , div [ classes [ textRight ] ]
            -- TODO: check loading spinner (at very least close modal)
            [ button
                [ classes [ btn, btnSecondary, uppercase, spaceRight ]
                , onClick $ const $ Just Cancel
                ]
                [ text "Cancel" ]
            , button
                [ classes [ btn, uppercase ]
                , disabled isEmpty
                , onClick $ const $ Just SaveProject
                ]
                [ text "Save" ]
            ]
        , renderError (state ^. _error)
        ]
    ]
  where
  renderError = case _ of
    Nothing -> text ""
    (Just err) -> div [ class_ (ClassName "error") ] [ text err ]

  isEmpty = state ^. _projectName == ""
