module ConfirmUnsavedNavigation.View where

import Prelude hiding (div)
import Halogen.HTML (ClassName(..), ComponentHTML, button, div, div_, p_, text)
import ConfirmUnsavedNavigation.Types as CN
import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen.Classes (btn, btnSecondary, modalContent, spaceRight, uppercase)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action(..), ChildSlots, State, _projectName)

render ::
  forall m.
  MonadAff m =>
  Action ->
  State ->
  ComponentHTML Action ChildSlots m
render intendedAction state =
  div [ classes [ modalContent, ClassName "confirm-unsaved-navigation" ] ]
    [ p_ [ text "Clicking on the Marlowe logo will take you out of the editor and return you to the home page." ]
    , p_ [ text "Unsaved changes will be lost." ]
    , p_ [ text $ "Do you want to save changes to '" <> (state ^. _projectName) <> "'?" ]
    , div [ classes [ ClassName "actions" ] ]
        [ div_
            [ button [ classes [ btn, btnSecondary, uppercase ], onConfirm CN.Cancel ] [ text "Cancel" ]
            ]
        , div_
            [ button [ classes [ btn, btnSecondary, uppercase, spaceRight ], onConfirm CN.DontSaveProject ] [ text "Don't Save" ]
            , button [ classes [ btn, uppercase ], onConfirm CN.SaveProject ] [ text "Save" ]
            ]
        ]
    ]
  where
  onConfirm msg = onClick $ const $ Just $ ConfirmUnsavedNavigationAction intendedAction msg
