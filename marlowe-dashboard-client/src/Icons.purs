-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( add
  , close
  , contacts
  , east
  , help
  , home
  , menu
  , next
  , pay
  , previous
  , roles
  , terms
  , wallet
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (class_)

icon :: forall p i. String -> HTML p i
icon str = span [ class_ $ ClassName "material-icons-round" ] [ text str ]

-----
add :: forall p i. HTML p i
add = icon "add"

close :: forall p i. HTML p i
close = icon "close"

contacts :: forall p i. HTML p i
contacts = icon "person"

east :: forall p i. HTML p i
east = icon "east"

help :: forall p i. HTML p i
help = icon "help"

home :: forall p i. HTML p i
home = icon "home"

menu :: forall p i. HTML p i
menu = icon "short_text"

next :: forall p i. HTML p i
next = icon "chevron_right"

pay :: forall p i. HTML p i
pay = icon "credit_score"

previous :: forall p i. HTML p i
previous = icon "chevron_left"

roles :: forall p i. HTML p i
roles = icon "person_pin_circle"

terms :: forall p i. HTML p i
terms = icon "alarm_add"

wallet :: forall p i. HTML p i
wallet = icon "layers"
