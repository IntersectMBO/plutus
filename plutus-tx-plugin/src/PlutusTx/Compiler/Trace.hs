{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Compiler.Trace where

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils

import PlutusCore qualified as PLC
import PlutusIR qualified as PIR

import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Set qualified as Set
import Data.Text (Text)
import Debug.Trace
import GHC.Plugins qualified as GHC

{-| A combination of `withContextM` and `traceCompilationStep`.

`withContextM` emits a stack trace when the compilation fails, and can be
turned on via `-fcontext-level=<level>`.

`traceCompilationStep` dumps the full compilation trace, and can be
turned on via `-fdump-compilation-trace`.
-}
traceCompilation
  :: ( MonadReader (CompileContext uni fun) m
     , MonadState CompileState m
     , MonadError (WithContext Text e) m
     )
  => Int
  -- ^ Context level
  -> GHC.SDoc
  -- ^ The thing (expr, type, kind, etc.) being compiled
  -> m a
  -- ^ The compilation action
  -> m a
traceCompilation p sd = withContextM p (sdToTxt sd) . traceCompilationStep sd

traceCompilationStep
  :: (MonadReader (CompileContext uni fun) m, MonadState CompileState m)
  => GHC.SDoc
  -- ^ The thing (expr, type, kind, etc.) being compiled
  -> m a
  -- ^ The compilation action
  -> m a
traceCompilationStep sd compile = ifM (notM (asks ccDebugTraceOn)) compile $ do
  compileState@(CompileState{csNextStep = nextStep, csPreviousSteps = prevSteps}) <- get
  put $ compileState {csNextStep = (nextStep + 1), csPreviousSteps = (nextStep : prevSteps)}
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
  modify' $ \compileState'@(CompileState {csPreviousSteps = prevSteps'}) ->
    compileState' {csPreviousSteps = drop 1 prevSteps'}
  pure res

pushCallStack :: MonadState CompileState m => GHC.Var -> m a -> m a
pushCallStack expr x = do
  origCallStack <- gets csCallStack
  modify' $ \compileState@(CompileState {csCallStack = callstack}) ->
    compileState {csCallStack = (expr : callstack)}
  res <- x
  modify' $ \compileState -> compileState {csCallStack = origCallStack}
  pure res

lastCallStackName :: MonadState CompileState m => m (Maybe (PIR.Name))
lastCallStackName = do
  names <- gets csCallStackNames
  pure $ case names of
    []    -> Nothing
    (x:_) -> Just x

bob :: (PLC.MonadQuote m, MonadState CompileState m) => m a -> m a
bob x = do
  callstack <- PLC.freshName "callstack"
  origNames <- gets csCallStackNames
  modify' $ \compileState@(CompileState {csCallStackNames = names}) ->
    compileState {csCallStackNames = (callstack : names)}
  res <- x
  modify' $ \compileState -> compileState {csCallStackNames = origNames}
  pure res

insertCallStackFunctionName :: MonadState CompileState m => LexName -> m ()
insertCallStackFunctionName name =
  modify' $ \compileState@(CompileState {csCallStackFunctions = fns}) ->
    compileState {csCallStackFunctions = Set.insert name fns}
