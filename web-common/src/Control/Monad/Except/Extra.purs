module Control.Monad.Except.Extra where

import Prologue
import Control.Monad.Except (except)
import Control.Monad.Except.Trans (ExceptT)
import Data.Either (note)

noteT :: forall m e a. Applicative m => e -> Maybe a -> ExceptT e m a
noteT e = except <<< note e
