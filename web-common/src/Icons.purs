module Icons where

import Halogen.HTML (ClassName(ClassName), HTML, i)
import Halogen.HTML.Properties (class_)

data Icon
  = CreditCard
  | LongArrowAltDown
  | ArrowUp
  | ArrowRight
  | ArrowDown
  | ArrowLeft
  | Bars
  | Close
  | Check
  | Bitcoin
  | Clipboard
  | Github
  | Plus
  | Trash
  | Spinner
  | SignInAlt
  | Infinity
  | Play
  | Reverse
  | StepBackward
  | StepForward
  | Hourglass
  | HourglassStart
  | HourglassEnd
  | CheckCircle
  | ExclamationCircle

icon :: forall p i. Icon -> HTML p i
icon iconType = i [ class_ (iconClass iconType) ] []

iconClass :: Icon -> ClassName
iconClass CreditCard = ClassName "fa fa-credit-card"

iconClass LongArrowAltDown = ClassName "fa fa-long-arrow-alt-down"

iconClass ArrowUp = ClassName "fa fa-arrow-up"

iconClass ArrowRight = ClassName "fa fa-arrow-right"

iconClass ArrowDown = ClassName "fa fa-arrow-down"

iconClass ArrowLeft = ClassName "fa fa-arrow-left"

iconClass Bars = ClassName "fa fa-bars"

iconClass Close = ClassName "fa fa-times"

iconClass Check = ClassName "fa fa-check"

iconClass Bitcoin = ClassName "fab fa-bitcoin"

iconClass Clipboard = ClassName "fa fa-clipboard"

iconClass Github = ClassName "fab fa-github"

iconClass Plus = ClassName "fa fa-plus"

iconClass Trash = ClassName "fa fa-trash"

iconClass Spinner = ClassName "fa fa-spinner fa-pulse"

iconClass SignInAlt = ClassName "fa fa-sign-in-alt"

iconClass Infinity = ClassName "fa fa-infinity"

iconClass Play = ClassName "fa fa-play"

iconClass Reverse = ClassName "fa fa-play fa-flip-horizontal"

iconClass StepBackward = ClassName "fa fa-step-backward"

iconClass StepForward = ClassName "fa fa-step-forward"

iconClass Hourglass = ClassName "fa fa-hourglass"

iconClass HourglassStart = ClassName "fa fa-hourglass-start"

iconClass HourglassEnd = ClassName "fa fa-hourglass-end"

iconClass CheckCircle = ClassName "fa fa-check-circle"

iconClass ExclamationCircle = ClassName "fa fa-exclamation-circle"
