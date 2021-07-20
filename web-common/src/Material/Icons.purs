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
  | AddBox
  | AddCircle
  | ArrowRight
  | ArrowLeft
  | Close
  | Contacts
  | Contract
  | ContractContractForDifferences
  | ContractLoan
  | ContractPurchase
  | Copy
  | Done
  | DoneWithCircle
  | ErrorOutline
  | Help
  | HelpOutline
  | History
  | Home
  | Info
  | Language
  | Menu
  | Next
  | NewContact
  | Pay
  | Play
  | Previous
  | Refresh
  | Roles
  | Running
  | South
  | TaskAlt
  | Terms
  | Timer
  | Tutorials

content :: Icon -> String
content Add = "add"

content AddBox = "add_box"

content AddCircle = "add_circle"

content ArrowRight = "east"

content ArrowLeft = "west"

content Close = "close"

content Contacts = "people"

content Contract = "history_edu"

content ContractContractForDifferences = "trending_up"

content ContractLoan = "wrap_text" -- FIXME: this is the wrong icon (I can't find the right one)

content ContractPurchase = "swap_horiz"

content Copy = "copy_content"

content Done = "done"

content DoneWithCircle = "check_circle_outline"

content ErrorOutline = "error_outline"

content Help = "help"

content HelpOutline = "help_outline"

content History = "history"

content Home = "home"

content Info = "info"

content Language = "language"

content Menu = "short_text"

content Next = "chevron_right"

content NewContact = "person_add_alt"

content Pay = "credit_score"

content Play = "play_arrow"

content Previous = "chevron_left"

content Refresh = "refresh"

content Roles = "person_pin_circle"

content Running = "directions_run"

content South = "south"

content TaskAlt = "task_alt"

content Terms = "drive_file_rename_outline"

content Timer = "timer"

content Tutorials = "school"

iconClass :: Icon -> String
iconClass Add = "add"

iconClass AddBox = "add-box"

iconClass AddCircle = "add-circle"

iconClass ArrowRight = "arrow-right"

iconClass ArrowLeft = "arrow-left"

iconClass Close = "close"

iconClass Contacts = "contacts"

iconClass Contract = "contract"

iconClass ContractContractForDifferences = "contract-contract-for-differences"

iconClass ContractLoan = "contract-loan"

iconClass ContractPurchase = "contract-purchase"

iconClass Copy = "copy"

iconClass Done = "done"

iconClass DoneWithCircle = "check-circle-outline"

iconClass ErrorOutline = "error-outline"

iconClass Help = "help"

iconClass HelpOutline = "help-outline"

iconClass History = "history"

iconClass Home = "home"

iconClass Info = "info"

iconClass Language = "language"

iconClass Menu = "menu"

iconClass Next = "next"

iconClass NewContact = "new-contact"

iconClass Pay = "pay"

iconClass Play = "play"

iconClass Previous = "previous"

iconClass Refresh = "refresh"

iconClass Roles = "roles"

iconClass Running = "running"

iconClass South = "south"

iconClass TaskAlt = "task-alt"

iconClass Terms = "terms"

iconClass Timer = "timer"

iconClass Tutorials = "tutorials"
