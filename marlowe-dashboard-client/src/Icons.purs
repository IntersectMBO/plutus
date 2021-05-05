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
  | ArrowLeft
  | Close
  | Contacts
  | Done
  | DoneWithCircle
  | ErrorOutline
  | Help
  | Home
  | Menu
  | Next
  | NewContact
  | Pay
  | Previous
  | Roles
  | TaskAlt
  | Terms
  | Timer
  | Wallet

content :: Icon -> String
content Add = "add"

content AddCircle = "add_circle_outline"

content ArrowRight = "east"

content ArrowLeft = "west"

content Close = "close"

content Contacts = "people"

content Done = "done"

content DoneWithCircle = "check_circle_outline"

content ErrorOutline = "error_outline"

content Help = "help"

content Home = "home"

content Menu = "short_text"

content Next = "chevron_right"

content NewContact = "person_add_alt"

content Pay = "credit_score"

content Previous = "chevron_left"

content Roles = "person_pin_circle"

content TaskAlt = "task_alt"

content Terms = "alarm_add"

content Timer = "timer"

content Wallet = "account_balance_wallet"

iconClass :: Icon -> String
iconClass Add = "add"

iconClass AddCircle = "add-circle"

iconClass ArrowRight = "arrow-right"

iconClass ArrowLeft = "arrow-left"

iconClass Close = "close"

iconClass Contacts = "contacts"

iconClass Done = "done"

iconClass DoneWithCircle = "check-circle-outline"

iconClass ErrorOutline = "error-outline"

iconClass Help = "help"

iconClass Home = "home"

iconClass Menu = "menu"

iconClass Next = "next"

iconClass NewContact = "new-contact"

iconClass Pay = "pay"

iconClass Previous = "previous"

iconClass Roles = "roles"

iconClass TaskAlt = "task-alt"

iconClass Terms = "terms"

iconClass Timer = "timer"

iconClass Wallet = "wallet"
