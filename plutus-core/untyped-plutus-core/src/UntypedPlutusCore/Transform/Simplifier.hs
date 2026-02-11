module UntypedPlutusCore.Transform.Simplifier
  ( SimplifierT (..)
  , Trace.SimplifierTrace (..)
  , Trace.SimplifierStage (..)
  , Trace.Simplification (..)
  , runSimplifierT
  , evalSimplifierT
  , execSimplifierT
  , Simplifier
  , runSimplifier
  , evalSimplifier
  , execSimplifier
  , Trace.initSimplifierTrace
  , recordSimplification
  , recordSimplificationWithHints
  ) where

import Control.Monad.State (MonadTrans, StateT)
import Control.Monad.State qualified as State

import Control.Monad.Identity (Identity, runIdentity)
import PlutusCore.Quote (MonadQuote)
import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Hints
import UntypedPlutusCore.Transform.Certify.Trace qualified as Trace

newtype SimplifierT name uni fun ann m a
  = SimplifierT
  { getSimplifierT :: StateT (Trace.SimplifierTrace name uni fun ann) m a
  }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance MonadQuote m => MonadQuote (SimplifierT name uni fun ann m)

runSimplifierT
  :: SimplifierT name uni fun ann m a
  -> m (a, Trace.SimplifierTrace name uni fun ann)
runSimplifierT = flip State.runStateT Trace.initSimplifierTrace . getSimplifierT

evalSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m a
evalSimplifierT = flip State.evalStateT Trace.initSimplifierTrace . getSimplifierT

execSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m (Trace.SimplifierTrace name uni fun ann)
execSimplifierT = flip State.execStateT Trace.initSimplifierTrace . getSimplifierT

type Simplifier name uni fun ann = SimplifierT name uni fun ann Identity

runSimplifier :: Simplifier name uni fun ann a -> (a, Trace.SimplifierTrace name uni fun ann)
runSimplifier = runIdentity . runSimplifierT

evalSimplifier :: Simplifier name uni fun ann a -> a
evalSimplifier = runIdentity . evalSimplifierT

execSimplifier :: Simplifier name uni fun ann a -> Trace.SimplifierTrace name uni fun ann
execSimplifier = runIdentity . execSimplifierT

recordSimplification
  :: Monad m
  => Term name uni fun a
  -> Trace.SimplifierStage
  -> Term name uni fun a
  -> SimplifierT name uni fun a m ()
recordSimplification = recordSimplificationWithHints Hints.NoHints

recordSimplificationWithHints
  :: Monad m
  => Hints.Hints
  -> Term name uni fun a
  -> Trace.SimplifierStage
  -> Term name uni fun a
  -> SimplifierT name uni fun a m ()
recordSimplificationWithHints hints before stage after =
  let simplification = Trace.Simplification before stage hints after
   in SimplifierT . State.modify' $ \st ->
        st {Trace.simplifierTrace = simplification : Trace.simplifierTrace st}
