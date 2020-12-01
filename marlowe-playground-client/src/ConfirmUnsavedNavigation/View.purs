module ConfirmUnsavedNavigation.View where

import Halogen.HTML
import Bootstrap (btnSecondary, btn)
import ConfirmUnsavedNavigation.Types as CN
import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen.Classes (modalContent, spaceRight)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (Action(..), ChildSlots, State, _projectName)
import Prelude (const, ($), (<>))

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
            [ button [ classes [ btn, btnSecondary ], onClick $ const $ Just cancel ] [ text "CANCEL" ]
            ]
        , div_
            [ button [ classes [ btn, btnSecondary, spaceRight ], onClick $ const $ Just dontSave ] [ text "DON'T SAVE" ]
            , button [ class_ (btn), onClick $ const $ Just save ] [ text "SAVE" ]
            ]
        ]
    ]
  where
  cancel = ConfirmUnsavedNavigationAction intendedAction CN.Cancel

  dontSave = ConfirmUnsavedNavigationAction intendedAction CN.DontSaveProject

  save = ConfirmUnsavedNavigationAction intendedAction CN.SaveProject
