module Control.Coroutine.Extra where

import Control.Coroutine (Consumer)
import Control.Monad.Free.Trans (interpret)
import Data.Function ((<<<))
import Data.Functor (class Functor)
import Data.Profunctor (lcmap)

mapConsumer :: forall f a b r. Functor f => (a -> b) -> Consumer b f r -> Consumer a f r
mapConsumer = interpret <<< lcmap
