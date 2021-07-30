module LoadingSubmitButton.Lenses where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))

_caption :: forall s a. Lens' { caption :: a | s } a
_caption = prop (SProxy :: SProxy "caption")

_buttonHeight :: forall s a. Lens' { buttonHeight :: a | s } a
_buttonHeight = prop (SProxy :: SProxy "buttonHeight")

_styles :: forall s a. Lens' { styles :: a | s } a
_styles = prop (SProxy :: SProxy "styles")

_status :: forall s a. Lens' { status :: a | s } a
_status = prop (SProxy :: SProxy "status")

_enabled :: forall s a. Lens' { enabled :: a | s } a
_enabled = prop (SProxy :: SProxy "enabled")
