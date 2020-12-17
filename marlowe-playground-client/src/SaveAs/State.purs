module SaveAs.State where

import Data.Lens (assign, (^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (activeBorderBlue700, border, borderBlue300, btn, btnSecondary, fontSemibold, fullWidth, modalContent, noMargins, spaceBottom, spaceLeft, spaceRight, spaceTop, textBase, textRight, textSm, uppercase)
import Halogen.HTML (button, div, h2, input, text)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, placeholder, value)
import Icons (Icon(..), icon)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Network.RemoteData (RemoteData(..), isFailure, isLoading)
import Prelude (Unit, Void, const, pure, unit, ($), (<<<), (==), (||))
import Prim.TypeError (class Warn, Text)
import SaveAs.Types (Action(..), State, _projectName, _status)
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
  Warn (Text "We need to redesing the error message") =>
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes if isFailure' then [ ClassName "modal-error" ] else [] ]
    [ div [ classes [ spaceTop, spaceLeft ] ]
        [ h2 [ classes [ textBase, fontSemibold, noMargins ] ] [ text "Save as" ]
        ]
    , div [ classes [ modalContent, ClassName "save-as-modal" ] ]
        [ input
            [ classes [ spaceBottom, fullWidth, textSm, border, borderBlue300, activeBorderBlue700 ]
            , value (state ^. _projectName)
            , onValueInput (Just <<< ChangeInput)
            , placeholder "Type a name for your project"
            ]
        , div [ classes [ textRight ] ]
            [ button
                [ classes [ btn, btnSecondary, uppercase, spaceRight ]
                , onClick $ const $ Just Cancel
                ]
                [ text "Cancel" ]
            , button
                [ classes [ btn, uppercase ]
                , disabled $ isEmpty || isLoading'
                , onClick $ const $ Just SaveProject
                ]
                if isLoading' then [ icon Spinner ] else [ text "Save" ]
            ]
        , renderError (state ^. _status)
        ]
    ]
  where
  isLoading' = isLoading $ (state ^. _status)

  isFailure' = isFailure $ (state ^. _status)

  renderError = case _ of
    (Failure err) -> div [ class_ (ClassName "error") ] [ text err ]
    _ -> text ""

  isEmpty = state ^. _projectName == ""
