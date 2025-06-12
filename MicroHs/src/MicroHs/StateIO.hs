-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-unused-imports -Wno-dodgy-imports -Wno-noncanonical-monad-instances #-}
-- State monad over IO
module MicroHs.StateIO(
  module MicroHs.StateIO,
  module Control.Applicative,
  module Control.Monad,
  module Data.Functor,
  ) where
import qualified Prelude(); import MHSPrelude
import Control.Applicative
import Control.Monad
import Data.Functor hiding(unzip)

newtype StateIO s a = S (s -> IO (a,s))

runStateIO :: forall s a . StateIO s a -> (s -> IO (a,s))
runStateIO (S x) = x

execStateIO :: forall s a . StateIO s a -> s -> IO s
execStateIO sa s = do
  as <- runStateIO sa s
  case as of
    (_, ss) -> return ss

instance Functor (StateIO s) where
  fmap f sa = S $ \ s -> do
    (a, ss) <- runStateIO sa s
    return (f a, ss)

instance Applicative (StateIO s) where
  pure a = S $ \ s -> return (a, s)
  (<*>) = ap
  -- Hugs doesn't have *> here

instance Monad (StateIO s) where
  (>>=) m k = S $ \ s -> do
    (a, ss) <- runStateIO m s
    runStateIO (k a) ss
  (>>) m k = S $ \ s -> do
    (_, ss) <- runStateIO m s
    runStateIO k ss
  return = pure

{-
instance MonadFail (StateIO s) where
  fail = error
-}

gets :: forall s a . (s -> a) -> StateIO s a
gets f = S $ \ s -> return (f s, s)

modify :: forall s . (s -> s) -> StateIO s ()
modify f = S $ \ s -> return ((), f s)

put :: forall s . s -> StateIO s ()
put s = S $ \ _ -> return ((), s)

get :: forall s . StateIO s s
get = S $ \ s -> return (s, s)

liftIO :: forall s a . IO a -> StateIO s a
liftIO io = S $ \ s -> do
  a <- io
  return (a, s)
