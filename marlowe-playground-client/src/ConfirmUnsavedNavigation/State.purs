module ConfirmUnsavedNavigation.State where

import Halogen.HTML
import Bootstrap (btnSecondary, btn)
import ConfirmUnsavedNavigation.Types (Action(..), State, _wantsToSaveProject)
import Data.Lens (assign)
import Data.Maybe (Maybe(..))
import Debug.Trace (spy)
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM)
import Halogen.Classes (modalContent, spaceRight)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_)
import Prelude (Unit, Void, const, ($))
import Servant.PureScript.Settings (SPSettings_)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings DontSaveProject = do
  -- FIXME: remove log, and if possible the state
  assign _wantsToSaveProject $ spy "ConfirmUnsavedNavigation.handleAction DontSaveProject" false

handleAction settings _ = do
  -- FIXME: remove log, and if possible the state
  assign _wantsToSaveProject $ spy "ConfirmUnsavedNavigation.handleAction _" true

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ modalContent, ClassName "confirm-unsaved-navigation" ] ]
    [ p_ [ text "Clicking on the Marlowe logo will take you out of the editor and return you to the home page." ]
    , p_ [ text "Unsaved changes will be lost." ]
    {- FIXME: add the project name instead of untitled-}
    , p_ [ text "Do you want to save changes to 'Untitled'?" ]
    , div [ classes [ ClassName "actions" ] ]
        [ div_
            [ button [ classes [ btn, btnSecondary ], onClick $ const $ Just Cancel ] [ text "CANCEL" ]
            ]
        , div_
            [ button [ classes [ btn, btnSecondary, spaceRight ], onClick $ const $ Just DontSaveProject ] [ text "DON'T SAVE" ]
            , button [ class_ (btn), onClick $ const $ Just SaveProject ] [ text "SAVE" ]
            ]
        ]
    ]
