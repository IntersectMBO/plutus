{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver
  ( Breakpointable (..)
  , CekState
  , Cmd (..)
  , runDriverT
  , DebugF (..)
    -- | Reexport some functions for convenience
  , mkCekTrans
  , CekTrans
  , F.MonadFree
  , F.iterM
  , F.iterTM
  , F.partialIterT
  , F.cutoff
  , FreeT
  ) where

import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Control.Lens hiding (Context)
import Control.Monad (void)
import Control.Monad.Reader (MonadReader, ask, local, runReaderT)
import Control.Monad.Trans.Free as F
import Data.Function
import Data.Text

{- Note [Stepping the driver]

The client instructs the driver to do a single step of the Cek (`Step` Cmd) or multiple steps until
a condition is met (`Continue`,`Next`,`Finish`). The driver upon receiving a Command (via `inputF`)
fires a series of `stepF` actions to fulfill the command. A `stepF` action is supposed to move the
underlying CEK machine a *single* step forward. Since the driver is written as a free monad, the
interpretation of the `stepF` action is left open.

When the driver calls `stepF state`, it yields its coroutine with the current driver/cek state
(before the stepping interpretation). The interpreter of `stepF` receives the currentState and
calculates a newstate from it (e.g. **actually stepping the cek machine**). The interpreter then
resumes the driver coroutine with the new state.

The sensible interpretation to this is the CEK's state transition function (`cekTrans oldState
===> newState`), but other exotic options may be: logging the before/after states, or even
"mutating" the running program's variables in the environment before/after the state transition
(similar to C debuggers). The interpreter can even supply a different state transition function
(e.g. `id`), but we see little benefit in it at the moment. Currently all interpreters
(brick,repl,testing) just call`cekTrans`.
-}

{-| Leave abstract the types of annotation and breakpoints.
The only thing the driver requires is an inclusion relation of breakpoints into the Annotation -}
class Breakpointable ann bps | ann -> bps where
  -- MAYBE: we cannot know which breakpoint fired, return instead `Maybe Breakpoint`?
  hasBreakpoints :: ann -> bps -> Bool

-- | The commands that the driver may receive from the client (tui,cli,test,etc)
data Cmd bps
  = {-| Instruct the driver to a *SINGLE* step.
    Note: No need to pass breakpoints here because the stepping granularity is *minimal*. -}
    Step
  | -- | Instruct to multi-step until end-of-program or until breakpoint reached
    Continue bps
  | -- | Instruct to multi-step over the function call at point or until breakpoint reached
    Next bps
  | -- | Instruct to multi-step to end of current function or until breakpoint reached
    Finish bps
  deriving stock (Show, Read)

-- | The drivers's suspension functor
data DebugF uni fun ann bps a
  = -- | Await for the client (e.g. TUI) to tell what to do next (Cmd).
    InputF (Cmd bps -> a)
  | -- | The debug driver wants to log something
    DriverLogF Text a
  | {-| An enumeratee of Driver State (generator+iteratee):
    Yield a state before doing a step, then await for a state to resume after the step.
    See Note [Stepping the driver]. -}
    StepF
      (CekState uni fun ann)
      -- ^ yield with the current driver's state before running a step
      (CekState uni fun ann -> a)
      {-^ resume back with a state after the step interpretation
      | A generator of CekState to yield to client (e.g. TUI) -}
  | UpdateClientF (CekState uni fun ann) a
  deriving stock (Functor)

-- | The monad that the driver operates in
type Driving m uni fun ann bps =
  ( MonadReader (CekState uni fun ann) m -- the state of the debugger
  , MonadFree (DebugF uni fun ann bps) m -- the effects of the driver
  , Breakpointable ann bps
  )

-- | Entrypoint of the driver
runDriverT
  :: forall uni fun ann bps m
   . (Breakpointable ann bps, MonadFree (DebugF uni fun ann bps) m)
  => NTerm uni fun ann -> m ()
runDriverT = void . runReaderT driver . initState
  where
    initState :: NTerm uni fun ann -> CekState uni fun ann
    initState = Starting

-- | The driver action. The driver repeatedly:

---
-- 1) waits for a `Cmd`
-- 2) runs one or more CEK steps
-- 3) informs the client for CEK updates&logs
---
-- The driver computation exits when it reaches a CEK `Terminating` state.
driver :: Driving m uni fun ann bps => m ()
driver =
  inputF >>= \case
    -- Condition immediately satisfied
    Step -> multiStepUntil $ const True
    Continue bs -> multiStepUntil $ maybe False (`hasBreakpoints` bs) . cekStateAnn
    Next bs -> do
      startState <- ask
      multiStepUntil $ \curState ->
        maybe False (`hasBreakpoints` bs) (cekStateAnn curState)
          ||
          -- has activation record length been restored?
          let leCtx = onCtxLen (<)
           in curState `leCtx` startState
    Finish bs -> do
      startState <- ask
      multiStepUntil $ \curState ->
        maybe False (`hasBreakpoints` bs) (cekStateAnn curState)
          ||
          -- has activation record length become smaller?
          let ltCtx = onCtxLen (<=)
           in curState `ltCtx` startState
  where
    -- \| Comparison on states' contexts
    onCtxLen
      :: ( state ~ CekState uni fun ann
         , ctxLen ~ Maybe Word -- `Maybe` because ctx can be missing if terminating
         )
      => (ctxLen -> ctxLen -> a)
      -> state
      -> state
      -> a
    onCtxLen = (`on` preview (cekStateContext . to lenContext))

-- | Do one or more cek steps until Terminating state is reached or condition on 'CekState' is met.
multiStepUntil
  :: Driving m uni fun ann bp
  => (CekState uni fun ann -> Bool) -> m ()
multiStepUntil cond = do
  driverLogF "Driver is going to do a single step"
  newState <- stepF =<< ask
  case newState of
    Terminating {} ->
      -- don't recurse to driver, but EXIT the driver
      updateClientF newState
    _ ->
      -- update state
      local (const newState) $
        if cond newState
          then do
            updateClientF newState
            driver -- tail recurse
          else
            multiStepUntil cond -- tail recurse

-- * boilerplate "suspension actions"

-- Being in 'Driving' monad here is too constraining, but it does not matter.
inputF :: Driving m uni fun ann bps => m (Cmd bps)
inputF = liftF $ InputF id
driverLogF :: Driving m uni fun ann bps => Text -> m ()
driverLogF text = liftF $ DriverLogF text ()
updateClientF :: Driving m uni fun ann bps => CekState uni fun ann -> m ()
updateClientF dState = liftF $ UpdateClientF dState ()
stepF :: Driving m uni fun ann bps => CekState uni fun ann -> m (CekState uni fun ann)
stepF yieldState = liftF $ StepF yieldState id
