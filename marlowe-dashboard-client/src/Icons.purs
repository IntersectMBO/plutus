-- All available icons can be found here: https://material.io/resources/icons/?icon=timer&style=round
-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( add_
  , addCircle_
  , close_
  , close
  , contacts_
  , east_
  , help_
  , home_
  , menu_
  , next_
  , pay_
  , previous_
  , roles_
  , terms_
  , timer_
  , timer
  , wallet_
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (classes)
import Data.Array (cons)

icon_ :: forall p i. String -> HTML p i
icon_ str = icon str []

icon :: forall p i. String -> Array String -> HTML p i
icon str extraClasses = span [ classes $ ClassName <$> cons "material-icons-round" extraClasses ] [ text str ]

-----
add_ :: forall p i. HTML p i
add_ = icon_ "add"

addCircle_ :: forall p i. HTML p i
addCircle_ = icon_ "add_circle_outline"

close_ :: forall p i. HTML p i
close_ = icon_ "close"

close :: Array String -> forall p i. HTML p i
close = icon "close"

contacts_ :: forall p i. HTML p i
contacts_ = icon_ "person"

east_ :: forall p i. HTML p i
east_ = icon_ "east"

help_ :: forall p i. HTML p i
help_ = icon_ "help"

home_ :: forall p i. HTML p i
home_ = icon_ "home"

menu_ :: forall p i. HTML p i
menu_ = icon_ "short_text"

next_ :: forall p i. HTML p i
next_ = icon_ "chevron_right"

pay_ :: forall p i. HTML p i
pay_ = icon_ "credit_score"

previous_ :: forall p i. HTML p i
previous_ = icon_ "chevron_left"

roles_ :: forall p i. HTML p i
roles_ = icon_ "person_pin_circle"

terms_ :: forall p i. HTML p i
terms_ = icon_ "alarm_add"

timer_ :: forall p i. HTML p i
timer_ = icon_ "timer"

timer :: forall p i. Array String -> HTML p i
timer = icon "timer"

wallet_ :: forall p i. HTML p i
wallet_ = icon_ "layers"
