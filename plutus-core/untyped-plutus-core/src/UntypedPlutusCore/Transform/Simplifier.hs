{-# LANGUAGE PatternSynonyms #-}

module UntypedPlutusCore.Transform.Simplifier
  ( SimplifierT (..)
  , Trace.OptStage
  , pattern Trace.FloatDelayStage
  , pattern Trace.ForceDelayStage
  , pattern Trace.ForceCaseDelayStage
  , pattern Trace.CaseReduceStage
  , pattern Trace.InlineStage
  , pattern Trace.CseStage
  , pattern Trace.ApplyToCaseStage
  , pattern Trace.CaseOfCaseStage
  , pattern Trace.LetFloatOutStage
  , Trace.OptimizerTrace (..)
  , Trace.Optimization (..)
  , runSimplifierT
  , evalSimplifierT
  , execSimplifierT
  , Simplifier
  , runSimplifier
  , evalSimplifier
  , execSimplifier
  , Trace.initOptimizerTrace
  , recordOptimization
  , recordOptimizationWithHints
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
  { getSimplifierT :: StateT (Trace.OptimizerTrace name uni fun ann) m a
  }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance MonadQuote m => MonadQuote (SimplifierT name uni fun ann m)

runSimplifierT
  :: SimplifierT name uni fun ann m a
  -> m (a, Trace.OptimizerTrace name uni fun ann)
runSimplifierT = flip State.runStateT Trace.initOptimizerTrace . getSimplifierT

evalSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m a
evalSimplifierT = flip State.evalStateT Trace.initOptimizerTrace . getSimplifierT

execSimplifierT
  :: Monad m => SimplifierT name uni fun ann m a -> m (Trace.OptimizerTrace name uni fun ann)
execSimplifierT = flip State.execStateT Trace.initOptimizerTrace . getSimplifierT

type Simplifier name uni fun ann = SimplifierT name uni fun ann Identity

runSimplifier :: Simplifier name uni fun ann a -> (a, Trace.OptimizerTrace name uni fun ann)
runSimplifier = runIdentity . runSimplifierT

evalSimplifier :: Simplifier name uni fun ann a -> a
evalSimplifier = runIdentity . evalSimplifierT

execSimplifier :: Simplifier name uni fun ann a -> Trace.OptimizerTrace name uni fun ann
execSimplifier = runIdentity . execSimplifierT

recordOptimization
  :: Monad m
  => Term name uni fun a
  -> Trace.OptStage
  -> Term name uni fun a
  -> SimplifierT name uni fun a m ()
recordOptimization = recordOptimizationWithHints Hints.NoHints

recordOptimizationWithHints
  :: Monad m
  => Hints.Hints
  -> Term name uni fun a
  -> Trace.OptStage
  -> Term name uni fun a
  -> SimplifierT name uni fun a m ()
recordOptimizationWithHints hints before stage after =
  let simplification = Trace.Optimization before stage hints after
   in SimplifierT . State.modify' $ \st ->
        st {Trace.optimizerTrace = simplification : Trace.optimizerTrace st}
