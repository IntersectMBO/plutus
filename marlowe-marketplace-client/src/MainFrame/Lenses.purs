module MainFrame.Lenses
  ( _placeholder
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (State)

_placeholder :: Lens' State String
_placeholder = prop (SProxy :: SProxy "placeholder")
