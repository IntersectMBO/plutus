{-# LANGUAGE PatternSynonyms #-}

module UntypedPlutusCore.Transform.Optimizer
  ( OptimizerT (..)
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
  , runOptimizerT
  , evalOptimizerT
  , execOptimizerT
  , Optimizer
  , runOptimizer
  , evalOptimizer
  , execOptimizer
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

newtype OptimizerT name uni fun ann m a
  = OptimizerT
  { getOptimizerT :: StateT (Trace.OptimizerTrace name uni fun ann) m a
  }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance MonadQuote m => MonadQuote (OptimizerT name uni fun ann m)

runOptimizerT
  :: OptimizerT name uni fun ann m a
  -> m (a, Trace.OptimizerTrace name uni fun ann)
runOptimizerT = flip State.runStateT Trace.initOptimizerTrace . getOptimizerT

evalOptimizerT
  :: Monad m => OptimizerT name uni fun ann m a -> m a
evalOptimizerT = flip State.evalStateT Trace.initOptimizerTrace . getOptimizerT

execOptimizerT
  :: Monad m => OptimizerT name uni fun ann m a -> m (Trace.OptimizerTrace name uni fun ann)
execOptimizerT = flip State.execStateT Trace.initOptimizerTrace . getOptimizerT

type Optimizer name uni fun ann = OptimizerT name uni fun ann Identity

runOptimizer :: Optimizer name uni fun ann a -> (a, Trace.OptimizerTrace name uni fun ann)
runOptimizer = runIdentity . runOptimizerT

evalOptimizer :: Optimizer name uni fun ann a -> a
evalOptimizer = runIdentity . evalOptimizerT

execOptimizer :: Optimizer name uni fun ann a -> Trace.OptimizerTrace name uni fun ann
execOptimizer = runIdentity . execOptimizerT

recordOptimization
  :: Monad m
  => Term name uni fun a
  -> Trace.OptStage
  -> Term name uni fun a
  -> OptimizerT name uni fun a m ()
recordOptimization = recordOptimizationWithHints Hints.NoHints

recordOptimizationWithHints
  :: Monad m
  => Hints.Hints
  -> Term name uni fun a
  -> Trace.OptStage
  -> Term name uni fun a
  -> OptimizerT name uni fun a m ()
recordOptimizationWithHints hints before stage after =
  let optimization = Trace.Optimization before stage hints after
   in OptimizerT . State.modify' $ \st ->
        st {Trace.optimizerTrace = optimization : Trace.optimizerTrace st}
