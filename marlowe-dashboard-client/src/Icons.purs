-- All available icons can be found here: https://material.io/resources/icons/?icon=timer&style=round
-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( add
  , addCircle
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
  , timer
  , timer'
  , wallet
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (classes)
import Data.Array (cons)

icon :: forall p i. String -> HTML p i
icon str = icon' str []

-- The apostrophe helpers should we used when we need to apply other styles to the icons, as wrapping them
-- between a div or another span generates weird vertical alignment issues.
icon' :: forall p i. String -> Array String -> HTML p i
icon' str extraClasses = span [ classes $ ClassName <$> cons "material-icons-round" extraClasses ] [ text str ]

-----
add :: forall p i. HTML p i
add = icon "add"

addCircle :: forall p i. HTML p i
addCircle = icon "add_circle_outline"

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

timer :: forall p i. HTML p i
timer = icon "timer"

timer' :: forall p i. Array String -> HTML p i
timer' = icon' "timer"

wallet :: forall p i. HTML p i
wallet = icon "layers"
