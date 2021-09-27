-- | This module contains all the public API types for the component.
module Component.Modal.Types where

import Prologue
import Data.Lens (Prism', prism')
import Data.Tuple (uncurry)

data State a
  = Initial
  | Active Boolean a

_Active :: forall a. Prism' (State a) (Tuple Boolean a)
_Active =
  prism' (uncurry Active) case _ of
    Active open a -> Just $ Tuple open a
    _ -> Nothing
