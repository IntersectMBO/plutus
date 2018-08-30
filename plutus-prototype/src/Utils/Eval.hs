{-# OPTIONS -Wall #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Utils.Eval where

import           Control.Monad.Except
import           Control.Monad.Reader

type Evaluator e = ReaderT e (Either String)

environment :: Evaluator e e
environment = ask

class Eval e a where
  eval :: a -> Evaluator e a

class ParamEval p e a | e a -> p where
  paramEval :: p -> a -> Evaluator e a

class (MonadReader r m, MonadError e m)
   => MEval r e m a | m -> r, m -> e where
  meval :: a -> m a

class (MonadReader r m, MonadError e m)
   => PMEval p r e m a | m -> r, m -> e where
  pmeval :: p -> a -> m a
