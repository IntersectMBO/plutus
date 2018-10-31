module Icons where

import Halogen.HTML (ClassName(ClassName), HTML, i)
import Halogen.HTML.Properties (classes)

data Icon
  = CreditCard
  | LongArrowDown

icon :: forall p i. Icon -> HTML p i
icon iconType =
  i [ classes [ ClassName "fa", iconClass iconType ] ]
    []

iconClass :: Icon -> ClassName
iconClass CreditCard = ClassName "fa-credit-card"
iconClass LongArrowDown = ClassName "fa-long-arrow-down"
