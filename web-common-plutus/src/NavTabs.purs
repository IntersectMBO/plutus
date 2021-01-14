module NavTabs where

import Bootstrap (active, container, hidden, navItem_, navLink, navTabs_)
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen.HTML (HTML, a, div, div_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, id_)
import Prelude (class Eq, class Show, const, show, ($), (<$>), (<>), (==))

mainTabBar ::
  forall view r p i.
  Eq view =>
  Show view =>
  (view -> i) ->
  Array
    { link :: view
    , title :: String
    | r
    } ->
  view -> HTML p i
mainTabBar mkAction tabs activeView =
  div_
    [ navTabs_ (mkTab <$> tabs) ]
  where
  mkTab { link, title } =
    navItem_
      [ a
          [ id_ $ "tab-" <> String.toLower (show link)
          , classes $ [ navLink ] <> activeClass
          , onClick $ const $ Just $ mkAction link
          ]
          [ text title ]
      ]
    where
    activeClass =
      if link == activeView then
        [ active ]
      else
        []

viewContainer :: forall view p i. Eq view => view -> view -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView =
  if currentView == targetView then
    div [ classes [ container ] ]
  else
    div [ classes [ container, hidden ] ]
