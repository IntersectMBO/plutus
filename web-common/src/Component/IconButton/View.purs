module Component.IconButton.View (iconButton) where

import Prologue
import Data.Maybe (isNothing)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Material.Icons (Icon, icon_)

iconButton :: forall w action. Icon -> Maybe action -> HH.HTML w action
iconButton ic onClick =
  HH.button
    [ HP.disabled $ isNothing onClick
    , HE.onClick (const onClick)
    ]
    [ icon_ ic ]
