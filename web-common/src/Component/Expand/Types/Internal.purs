module Component.Expand.Types.Internal where

import Component.Expand.Types (Action, ComponentHTML, State)
import Halogen as H

type InnerState parentSlots parentAction m
  = { state :: State
    , render :: State -> ComponentHTML parentSlots parentAction m
    }

type DSL parentSlots parentAction m a
  = H.HalogenM (InnerState parentSlots parentAction m)
      (Action parentSlots parentAction m)
      parentSlots
      parentAction
      m
      a
