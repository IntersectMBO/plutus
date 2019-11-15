module Control.Monad.Maybe.Extra where

import Control.Applicative (class Applicative, pure)
import Control.Monad.Maybe.Trans (MaybeT(..))
import Data.Function ((<<<))
import Data.Maybe (Maybe)

hoistMaybe :: forall m a. Applicative m => Maybe a -> MaybeT m a
hoistMaybe = MaybeT <<< pure
