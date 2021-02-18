{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}

module Control.Monad.Freer.Extras.State (
      use
    , assign
    , modifying ) where

import           Control.Lens              (ASetter, Getting, over, set, view)
import           Control.Monad.Freer       (Eff, Member)
import           Control.Monad.Freer.State (State, get, gets, put)

use :: Member (State s) effs => Getting a s a -> Eff effs a
use accessor = gets (view accessor)

assign :: Member (State s) effs => ASetter s s a b -> b -> Eff effs ()
assign accessor value = get >>= put . set accessor value

modifying :: Member (State s) effs => ASetter s s a b -> (a -> b) -> Eff effs ()
modifying accessor f = get >>= put . over accessor f
