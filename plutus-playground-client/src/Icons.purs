module Icons where

import Halogen.HTML (ClassName(ClassName), HTML, i)
import Halogen.HTML.Properties (classes)

data Icon
  = CreditCard
  | LongArrowDown
  | Close
  | Check
  | Bitcoin
  | Github
  | Plus
  | Trash
  | Spinner
  | SignIn

icon :: forall p i. Icon -> HTML p i
icon iconType =
  i [ classes [ ClassName "fa", iconClass iconType ] ]
    []

iconClass :: Icon -> ClassName
iconClass CreditCard = ClassName "fa-credit-card"
iconClass LongArrowDown = ClassName "fa-long-arrow-down"
iconClass Close = ClassName "fa-close"
iconClass Check = ClassName "fa-check"
iconClass Bitcoin = ClassName "fa-bitcoin"
iconClass Github = ClassName "fa-github"
iconClass Plus = ClassName "fa-plus"
iconClass Trash = ClassName "fa-trash"
iconClass Spinner = ClassName "fa-spinner fa-pulse"
iconClass SignIn = ClassName "fa-sign-in"
