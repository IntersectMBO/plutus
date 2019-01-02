{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Optimizer (simplify) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.Optimizer.DeadCode as DeadCode
import qualified Language.PlutusIR.Optimizer.Merge    as Merge

import           Control.Monad
import           Control.Monad.Reader

-- | Perform some simplification of a 'Term'.
simplify :: MonadReader (CompilationCtx a) m => Term TyName Name b -> m (Term TyName Name b)
simplify = runIfOpts (pure . DeadCode.removeDeadBindings >=> pure . Merge.mergeLets)
