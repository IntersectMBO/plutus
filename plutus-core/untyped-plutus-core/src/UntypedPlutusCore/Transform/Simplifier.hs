{-# LANGUAGE NamedFieldPuns #-}

module UntypedPlutusCore.Transform.Simplifier
  ( SimplifierT (..)
  , SimplifierTrace (..)
  , SimplifierStage (..)
  , Simplification (..)
  , runSimplifierT
  , evalSimplifierT
  , execSimplifierT
  , Simplifier
  , runSimplifier
  , evalSimplifier
  , execSimplifier
  , initSimplifierTrace
  , recordSimplification
  ) where

import Control.Monad.State (MonadTrans, StateT)
import Control.Monad.State qualified as State

import Control.Monad.Identity (Identity, runIdentity)
import PlutusCore.Quote (MonadQuote)
import UntypedPlutusCore.Core.Type (Term)

newtype SimplifierT name uni fun ann m a
  = SimplifierT
  { getSimplifierT :: StateT (SimplifierTrace name uni fun ann) m a
  }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance MonadQuote m => MonadQuote (SimplifierT name uni fun ann m)

runSimplifierT
  :: SimplifierT name uni fun ann m a
  -> m (a, SimplifierTrace name uni fun ann)
runSimplifierT = flip State.runStateT initSimplifierTrace . getSimplifierT

evalSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m a
evalSimplifierT = flip State.evalStateT initSimplifierTrace . getSimplifierT

execSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m (SimplifierTrace name uni fun ann)
execSimplifierT = flip State.execStateT initSimplifierTrace . getSimplifierT

type Simplifier name uni fun ann = SimplifierT name uni fun ann Identity

runSimplifier :: Simplifier name uni fun ann a -> (a, SimplifierTrace name uni fun ann)
runSimplifier = runIdentity . runSimplifierT

evalSimplifier :: Simplifier name uni fun ann a -> a
evalSimplifier = runIdentity . evalSimplifierT

execSimplifier :: Simplifier name uni fun ann a -> SimplifierTrace name uni fun ann
execSimplifier = runIdentity . execSimplifierT

data SimplifierStage
  = FloatDelay
  | ForceDelay
  | ForceCaseDelay
  | CaseOfCase
  | CaseReduce
  | Inline
  | CSE
  | CaseApply

data Simplification name uni fun a
  = Simplification
  { beforeAST :: Term name uni fun a
  , stage :: SimplifierStage
  , afterAST :: Term name uni fun a
  }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype SimplifierTrace name uni fun a
  = SimplifierTrace
  { simplifierTrace
      :: [Simplification name uni fun a]
  }

initSimplifierTrace :: SimplifierTrace name uni fun a
initSimplifierTrace = SimplifierTrace []

recordSimplification
  :: Monad m
  => Term name uni fun a
  -> SimplifierStage
  -> Term name uni fun a
  -> SimplifierT name uni fun a m ()
recordSimplification beforeAST stage afterAST =
  let simplification = Simplification {beforeAST, stage, afterAST}
   in modify $ \st ->
        st {simplifierTrace = simplification : simplifierTrace st}
  where
    modify f = SimplifierT $ State.modify' f
