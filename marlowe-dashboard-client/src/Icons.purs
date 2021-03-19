-- All available icons can be found here: https://material.io/resources/icons/?icon=timer&style=round
-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( icon
  , icon_
  , Icon(..)
  , iconClass
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (classes)
import Data.Array (cons)

icon :: forall p i. Icon -> Array String -> HTML p i
icon i extraClasses = span [ classes $ ClassName <$> cons "material-icons-round" extraClasses ] [ text $ content i ]

icon_ :: forall p i. Icon -> HTML p i
icon_ i = icon i []

-----
data Icon
  = Add
  | AddCircle
  | ArrowRight
  | Close
  | Contacts
  | Help
  | Home
  | Menu
  | Next
  | Pay
  | Previous
  | Roles
  | Terms
  | Timer
  | Wallet

content :: Icon -> String
content Add = "add"

content AddCircle = "add_circle_outline"

content ArrowRight = "east"

content Close = "close"

content Contacts = "people"

content Help = "help"

content Home = "home"

content Menu = "short_text"

content Next = "chevron_right"

content Pay = "credit_score"

content Previous = "chevron_left"

content Roles = "person_pin_circle"

content Terms = "alarm_add"

content Timer = "timer"

content Wallet = "account_balance_wallet"

iconClass :: Icon -> String
iconClass Add = "add"

iconClass AddCircle = "add-circle"

iconClass ArrowRight = "arrow-right"

iconClass Close = "close"

iconClass Contacts = "contacts"

iconClass Help = "help"

iconClass Home = "home"

iconClass Menu = "menu"

iconClass Next = "next"

iconClass Pay = "pay"

iconClass Previous = "previous"

iconClass Roles = "roles"

iconClass Terms = "terms"

iconClass Timer = "timer"

iconClass Wallet = "wallet"
