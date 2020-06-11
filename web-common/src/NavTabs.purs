module NavTabs where

import Bootstrap (active, container, hidden, navItem_, navLink, navTabs_)
import Bootstrap as Bootstrap
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen.HTML (ClassName(..), HTML, a, div, div_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, id_)
import Prelude (class Eq, class Show, const, show, ($), (<$>), (<>), (==))

mainTabBar ::
  forall view r p i.
  Eq view =>
  Show view =>
  (view -> i) ->
  Array
    { help :: String
    , link :: view
    , title :: String
    | r
    } ->
  view -> HTML p i
mainTabBar mkAction tabs activeView =
  div_
    [ navTabs_ (mkTab <$> tabs)
    , div [ class_ $ ClassName "tab-help" ]
        [ helpText ]
    ]
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

  helpText = case Array.find (\({ link }) -> link == activeView) tabs of
    Nothing -> Bootstrap.empty
    Just { help } -> text help

viewContainer :: forall view p i. Eq view => view -> view -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView =
  if currentView == targetView then
    div [ classes [ container ] ]
  else
    div [ classes [ container, hidden ] ]
