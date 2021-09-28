-- | This module contains all the public API types for the component.
module Component.Modal.Types where

import Prologue
import Data.Lens (Prism', prism')
import Data.Tuple (uncurry)

data State a
  = Initial
  | Active a Boolean

_Active :: forall a. Prism' (State a) (Tuple a Boolean)
_Active =
  prism' (uncurry Active) case _ of
    Active a open -> Just $ Tuple a open
    _ -> Nothing
