-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( add
  , close
  , contacts
  , contracts
  , home
  , menu
  , rightArrow
  , wallet
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (class_)

icon :: forall p i. String -> HTML p i
icon str = span [ class_ $ ClassName "material-icons round" ] [ text str ]

-----
add :: forall p i. HTML p i
add = icon "add"

close :: forall p i. HTML p i
close = icon "close"

contacts :: forall p i. HTML p i
contacts = icon "person"

contracts :: forall p i. HTML p i
contracts = icon "history_edu"

home :: forall p i. HTML p i
home = icon "home"

menu :: forall p i. HTML p i
menu = icon "short_text"

rightArrow :: forall p i. HTML p i
rightArrow = icon "navigate_next"

wallet :: forall p i. HTML p i
wallet = icon "layers"
