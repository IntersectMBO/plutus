{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Compiler.Trace where

import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils

import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Debug.Trace
import GHC.Plugins qualified as GHC

traceCompilation ::
  (MonadReader (CompileContext uni fun) m, MonadState CompileState m) =>
  -- | The thing (expr, type, kind, etc.) being compiled
  GHC.SDoc ->
  -- | The compilation action
  m a ->
  m a
traceCompilation sd compile = ifM (notM (asks ccDebugTraceOn)) compile $ do
  CompileState nextStep prevSteps <- get
  put $ CompileState (nextStep + 1) (nextStep : prevSteps)
  let mbParentStep = listToMaybe prevSteps
  s <- sdToStr sd
  traceM $
    "<Step "
      <> show nextStep
      <> maybe "" (\parentStep -> ", Parent Step: " <> show parentStep) mbParentStep
      <> ">"
  traceM s
  res <- compile
  traceM $
    "<Completed step "
      <> show nextStep
      <> maybe "" (\parentStep -> ", Returning to step " <> show parentStep) mbParentStep
      <> ">"
  pure res
