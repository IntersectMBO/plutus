module Component.IconButton.View (iconButton) where

import Prologue
import Component.Icons (Icon, icon_)
import Data.Maybe (isNothing)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

iconButton :: forall w action. Icon -> Maybe action -> HH.HTML w action
iconButton ic onClick =
  HH.button
    [ HP.disabled $ isNothing onClick
    , HE.onClick (const onClick)
    ]
    [ icon_ ic ]
