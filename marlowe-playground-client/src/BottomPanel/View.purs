module BottomPanel.View (render) where

import Prelude hiding (div)
import Bootstrap (hidden)
import BottomPanel.Types (Action(..), State, _panelView, _showBottomPanel)
import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen.Classes (accentBorderTop, borderSeparator, boxShadowInverted, closeDrawerArrowIcon, collapsed, flex, flexCol, flexShrink0, fontBold, fullHeight, justifyBetween, minH0, minimizeIcon, paddingX, scroll, smallPaddingRight, smallPaddingTop, smallPaddingY, spaceX, textInactive, textSecondary)
import Halogen.HTML (ClassName, HTML, a, div, img, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, classes, src)

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
  -- The panelContent function receives the active panel and returns it's content. The `action` type parameter
  -- is what allow us to fire an action from the child that is intended to be interpreted on the parent.
  (panel -> HTML p (Action panel action)) ->
  State panel ->
  HTML p (Action panel action)
render panelTitles panelContent state =
  div [ classes ([ boxShadowInverted, flex, flexCol, fullHeight ] <> collapseWhenHidden) ]
    -- Header
    [ div [ classes [ flexShrink0, smallPaddingTop, flex, justifyBetween ] ]
        -- Titles
        [ div [ classes [ borderSeparator ] ]
            ( panelTitles
                <#> \panelTitle ->
                    a
                      [ classes ([ fontBold, paddingX ] <> panelTitle.classes <> activeClasses panelTitle.view)
                      , onClick $ clickTitleAction panelTitle.view
                      ]
                      [ text panelTitle.title ]
            )
        -- Visibility toggle
        , div [ classes [ smallPaddingRight ] ]
            [ a [ onClick $ const $ Just $ SetVisibility (state ^. _showBottomPanel <<< to not) ]
                [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
            ]
        ]
    -- Panel contents
    , div [ classes ([ spaceX, smallPaddingY, accentBorderTop, scroll, minH0 ] <> dontDisplayWhenHidden) ]
        [ panelContent (state ^. _panelView)
        ]
    ]
  where
  -- When the user clicks on a panel title header, if it's the current view it toggles the
  -- visibility, and if not it changes to that panel (which also shows the panel if hidden)
  clickTitleAction view =
    if state ^. _panelView == view then
      const $ Just $ SetVisibility (state ^. _showBottomPanel <<< to not)
    else
      const $ Just $ ChangePanel $ view

  activeClasses view = if state ^. _panelView == view then [ textSecondary ] else [ textInactive ]

  dontDisplayWhenHidden = if state ^. _showBottomPanel then [] else [ hidden ]

  collapseWhenHidden = if state ^. _showBottomPanel then [] else [ collapsed ]
