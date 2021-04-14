module Toast.Lenses
  ( _mToast
  , _expanded
  ) where

import Toast.Types (State, Toast)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))

_mToast :: Lens' State (Maybe Toast)
_mToast = prop (SProxy :: SProxy "mToast")

_expanded :: Lens' State Boolean
_expanded = prop (SProxy :: SProxy "expanded")
