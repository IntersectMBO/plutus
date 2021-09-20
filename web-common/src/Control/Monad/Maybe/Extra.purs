module Control.Monad.Maybe.Extra where

import Prologue
import Control.Monad.Maybe.Trans (MaybeT(..))

hoistMaybe :: forall m a. Applicative m => Maybe a -> MaybeT m a
hoistMaybe = MaybeT <<< pure
