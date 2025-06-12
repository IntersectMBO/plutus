{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module MicroHs.State(
  module MicroHs.State,
  ) where
import Control.Monad
import Control.Monad.Fail
import MHSPrelude hiding (fail)
import Prelude qualified ()

newtype State s a = S (s -> (a, s))

instance Functor (State s) where
{-
  fmap f sa = S $ \ s ->
    case runState sa s of
      (a, ss) -> (f a, ss)
-}
  fmap f sa = sa >>= (return . f)  -- slightly faster

instance Applicative (State s) where
  pure a = S $ \ s -> (a, s)
  (<*>) = ap
  -- Hugs doesn't have *> here

instance Monad (State s) where
  (>>=) m k = S $ \ s ->
    case runState m s of
      (a, ss) -> runState (k a) ss
  (>>) m k = S $ \ s ->
    case runState m s of
      (_, ss) -> runState k ss
  return = pure

instance MonadFail (State s) where
  fail = error

runState :: forall s a . State s a -> (s -> (a,s))
runState (S x) = x

evalState :: forall s a . State s a -> (s -> a)
evalState sa = fst . runState sa

modify :: forall s . (s -> s) -> State s ()
modify f = S $ \ s -> ((), f s)

put :: forall s . s -> State s ()
put s = S $ const ((), s)

get :: forall s . State s s
get = S $ \ s -> (s, s)

gets :: forall s a . (s -> a) -> State s a
gets f = S $ \ s -> (f s, s)

