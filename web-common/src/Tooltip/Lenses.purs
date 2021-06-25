module Tooltip.Lenses where

import Prelude
import Data.Lens (Lens', Traversal')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))

_message :: forall s a. Lens' { message :: a | s } a
_message = prop (SProxy :: SProxy "message")

_active :: forall s a. Lens' { active :: a | s } a
_active = prop (SProxy :: SProxy "active")

_reference :: forall s a. Lens' { reference :: a | s } a
_reference = prop (SProxy :: SProxy "reference")

_placement :: forall s a. Lens' { placement :: a | s } a
_placement = prop (SProxy :: SProxy "placement")

_mPopperInstance :: forall s a. Lens' { mPopperInstance :: a | s } a
_mPopperInstance = prop (SProxy :: SProxy "mPopperInstance")
