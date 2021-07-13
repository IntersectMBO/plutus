module Hint.Lenses where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))

_content :: forall s a. Lens' { content :: a | s } a
_content = prop (SProxy :: SProxy "content")

_active :: forall s a. Lens' { active :: a | s } a
_active = prop (SProxy :: SProxy "active")

_reference :: forall s a. Lens' { reference :: a | s } a
_reference = prop (SProxy :: SProxy "reference")

_placement :: forall s a. Lens' { placement :: a | s } a
_placement = prop (SProxy :: SProxy "placement")

_mPopperInstance :: forall s a. Lens' { mPopperInstance :: a | s } a
_mPopperInstance = prop (SProxy :: SProxy "mPopperInstance")

_mGlobalClickSubscription :: forall s a. Lens' { mGlobalClickSubscription :: a | s } a
_mGlobalClickSubscription = prop (SProxy :: SProxy "mGlobalClickSubscription")
