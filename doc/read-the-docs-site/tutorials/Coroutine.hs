-- BLOCK1
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Coroutine where

import Control.Monad.Trans.Free
import Data.Text (Text)
import Prelude hiding (log)

data UPLCTerm
data Command = Step

-- BLOCK2
data RequestF a
  = StepF UPLCTerm (Maybe UPLCTerm -> a)
  | LogF Text a
  | InputF (Command -> a)
  deriving Functor

-- BLOCK3
type SteppableCekM = IO

step :: UPLCTerm -> SteppableCekM (Maybe UPLCTerm)
step = undefined

log :: Text -> SteppableCekM ()
log = undefined

input :: SteppableCekM Command
input = undefined

-- BLOCK4
handle :: RequestF a -> SteppableCekM a
handle = \case
  StepF term k -> step term >>= pure . k
  LogF text k  -> log text >> pure k
  InputF k     -> input >>= pure . k

-- BLOCK5
runSteppableCek :: FreeT RequestF SteppableCekM a -> SteppableCekM a
runSteppableCek userAction = do
  runFreeT userAction >>= \case
    Pure res -> pure res
    Free req -> handle req >>= runSteppableCek

-- BLOCK6
stepF :: Monad m => UPLCTerm -> FreeT RequestF m (Maybe UPLCTerm)
stepF term = liftF (StepF term id)

logF :: Monad m => Text -> FreeT RequestF m ()
logF text = liftF (LogF text ())

inputF :: Monad m => FreeT RequestF m Command
inputF = liftF (InputF id)

-- BLOCK7
userComputation :: UPLCTerm -> FreeT RequestF SteppableCekM ()
userComputation programToDebug = do
  cmd <- inputF
  case cmd of
    Step -> do
      logF "Received Step command"
      mProgram <- stepF programToDebug
      maybe (pure ()) userComputation mProgram

-- BLOCK8
