module BottomPanel.View (render) where

import Prelude hiding (div)
import BottomPanel.Types (Action(..), State, _panelView, _showBottomPanel)
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, flex, flexTen, footerPanelBg, minimizeIcon)
import Halogen.HTML (ClassName(..), HTML, a, a_, div, img, li, section, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, src)

type PanelTitle panel
  = { view :: panel
    , classes :: Array ClassName
    , title :: String
    }

render ::
  forall p panel action.
  -- The panel equality restriction allow us to identify the current selected panel.
  Eq panel =>
  -- panelTitles is an ordered list of the titles we'll show in the widget. The caller needs to provide a
  -- `title` name to display, the `view` that is selected when the title is clicked and a list
  -- of `classes` to optionally style the titles.
  Array (PanelTitle panel) ->
  -- The panelContents function receives the active panel and returns it's content. The `action` type parameter
  -- is what allow us to fire an action from the child that is intended to be interpreted on the parent.
  (panel -> HTML p (Action panel action)) ->
  State panel ->
  HTML p (Action panel action)
render panelTitles panelContents state =
  div
    ( [ classes
          ( if showingBottomPanel then
              [ ClassName "simulation-bottom-panel" ]
            else
              [ ClassName "simulation-bottom-panel", collapsed ]
          )
      ]
    )
    [ div [ classes [ flex, ClassName "flip-x", ClassName "full-height" ] ]
        [ div [ class_ flexTen ]
            [ div [ classes [ footerPanelBg, active ] ]
                [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
                    [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal, accentBorderBottom ] ]
                        [ ul [ class_ (ClassName "start-item") ]
                            [ li [ class_ (ClassName "minimize-icon-container") ]
                                [ a [ onClick $ const $ Just $ SetVisibility (state ^. _showBottomPanel <<< to not) ]
                                    [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                                ]
                            ]
                        , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                            ( panelTitles
                                <#> \panelTitle ->
                                    li
                                      [ classes (panelTitle.classes <> isActive panelTitle.view)
                                      , onClick $ const $ Just $ ChangePanel $ panelTitle.view
                                      ]
                                      [ a_ [ text panelTitle.title ] ]
                            )
                        ]
                    ]
                , panelContents (state ^. _panelView)
                ]
            ]
        ]
    ]
  where
  isActive view = state ^. _panelView <<< (activeClass (eq view))

  showingBottomPanel = state ^. _showBottomPanel
