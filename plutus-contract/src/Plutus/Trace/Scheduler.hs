{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-

Implements a scheduler for cooperative multitasking. The scheduler supports
system calls for suspending threads, sending messages to other threads, and
starting new threads. Threads have a priority (see note [Thread Priority]).
They can send and receive messages of a user-defined type. The scheduler is
implemented as handler of the 'Control.Monad.Freer.Coroutine.Yield' effect, and
threads are @freer-simple@ programs that use that effect.

-}
module Plutus.Trace.Scheduler(
    ThreadId
    , SysCall
    , MessageCall(..)
    , ThreadCall(..)
    , WithPriority(..)
    , Priority(..)
    , Tag
    , EmSystemCall
    , SuspendedThread
    , EmThread(..)
    , SchedulerState(..)
    -- * Thread API
    , runThreads
    , fork
    , sleep
    , exit
    -- * Etc.
    , mkThread
    , mkSysCall
    , SchedulerLog(..)
    , ThreadEvent(..)
    , StopReason(..)
    ) where


import           Control.Lens                     hiding (Empty)
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Control.Monad.Freer.Log          (LogMsg, logDebug)
import           Control.Monad.Freer.Reader
import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.HashMap.Strict              (HashMap)
import qualified Data.HashMap.Strict              as HashMap
import           Data.HashSet                     (HashSet)
import qualified Data.HashSet                     as HashSet
import           Data.Hashable                    (Hashable)
import           Data.Map                         as Map
import           Data.Sequence                    (Seq (..))
import qualified Data.Sequence                    as Seq
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..), Tagged (..))
import           GHC.Generics                     (Generic)
import           Plutus.Trace.Tag                 (Tag)

{- Note [Thread Tag]

Within the scheduler, threads are identified by their 'ThreadId'. The thread
ID is assigned at runtime when a new thread is started. So the thread ID
depends on the state of the scheduler at the time the thread is started.

This makes it hard to refer to individual threads outside of the scheduler,
for example, when we inspect the emulator log. To make it easier to find
threads later on in the log, each thread also has a user-defined tag. The
scheduler maintains a map of tags to thread IDs, so that we can send messages
to threads that we only know the tag of.

It is up to the user to ensure that tags are unique. If two threads have the
same tag, the functioning of the scheduler is not affected (each thread still
has its own mailbox), but the tag can no longer be used to uniquely identify a
thread. In practice however the number of interesting threads is small enough
that finding distinct tags for them is not a problem.

-}

-- | Unique identifier of a thread.
newtype ThreadId = ThreadId { unThreadId :: Int }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (Hashable, ToJSON, FromJSON)
    deriving Pretty via (Tagged "Thread" Int)

-- | ID of the first thread.
initialThreadId :: ThreadId
initialThreadId = ThreadId 0

{- Note [Thread Priority]

When a thread yields control it assigns itself one of three priorities. The
priority determines how long the thread goes to sleep for. The scheduler
maintains one queue of suspended threads for each priority.

In the emulator, we use thread priorities to drive the progress of simulated
time. See note [Simulator Time] in 'Plutus.Trace.Emulator.System' for details.

-}

{- Note [Freeze and Thaw]

Freezing and unfreezing use two slightly different mechanims.

To freeze a thread, that thread must suspend itself with the 'Frozen' priority.
If we want to be able to freeze a thread from the outside, we need to send it a
message instructing it to do so. (In the emulator, this is the 'Freeze'
constructor of 'Plutus.Trace.Emulator.Types.EmulatorMessage'.)

@
  mkSysCall @_ @EmulatorMessage Normal (Message threadId Freeze)
@


To unfreeze a thread, we use the 'Thaw' system call of the emulator.

@
  mkSysCall @_ @systemEvent Normal (Thaw threadId)
@

Note how the sytem event type in the first line is instantiated to
'EmulatorMessage', and in the second line it is free. The goal of this
somewhat roundabout approach is to avoid having to fish out the thread from the
queues of the scheduler state. Instead, we tell the thread to freeze itself, so
we don't have to mess with the queues.

-}

-- | Priority of a thread.
data Priority =
    Normal -- ^ Thread is ready to run
    | Sleeping -- ^ Thread is sleeping, to be resumed only after an external event happens
    | Frozen -- ^ Thread is frozen, it will only be resumed after it is manually unfrozen via the 'Thaw' sys call.
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)
    deriving Pretty via (PrettyShow Priority)

-- | A thread with a 'Priority'.
data WithPriority t
    = WithPriority
        { _priority :: Priority
        , _thread   :: t
        }

type SuspendedThread effs systemEvent = WithPriority (EmThread effs systemEvent)

type EmSystemCall effs systemEvent = WithPriority (SysCall effs systemEvent)

-- | Thread that can be run by the scheduler
data EmThread effs systemEvent =
    EmThread
        { _continuation :: Maybe systemEvent -> Eff effs (Status effs (EmSystemCall effs systemEvent) (Maybe systemEvent) ()) -- ^ The continuation to be run when the thread is resumed.
        , _threadId     :: ThreadId -- ^ Thread ID
        , _tag          :: Tag -- ^ Tag of the thread. See note [Thread Tag]
        }

-- | The system calls we can make to the scheduler, affecting the the threads
--   that are currently running.
data ThreadCall effs systemEvent
    = Fork (ThreadId -> SuspendedThread effs systemEvent) -- ^ Start a new thread with a new thread ID.
    | Thaw ThreadId -- ^ Unfreeze a thread.
    | Exit -- ^ Terminate the scheduler.

-- | Sending messages to other threads and waiting for new messages to arrive.
data MessageCall systemEvent
    = WaitForMessage -- ^ Suspend ourselves (the caller) until we receive a message
    | Broadcast systemEvent -- ^ Send a message to all threads
    | Message ThreadId systemEvent -- ^ Send a message to a specific thread

type SysCall effs systemEvent = Either (MessageCall systemEvent) (ThreadCall effs systemEvent)

makePrisms ''MessageCall
makePrisms ''ThreadCall

-- | Scheduler state
data SchedulerState effs systemEvent
    = SchedulerState
        { _normalPrio    :: Seq (EmThread effs systemEvent) -- ^  Threads running at normal priority
        , _sleeping      :: Seq (EmThread effs systemEvent) -- ^ Sleeping threads (waiting for an external event)
        , _frozen        :: Seq (EmThread effs systemEvent) -- ^ Frozen threads (will not be resumed until they are explicitly unfrozen)
        , _lastThreadId  :: ThreadId -- ^ Last thread id assigned to a thread
        , _mailboxes     :: HashMap ThreadId (Seq systemEvent) -- ^ The mailboxes of all active threads.
        , _activeThreads :: Map Tag (HashSet ThreadId) -- ^ Map of tags to thread IDs. See note [Thread Tag]
        }

makeLenses ''SchedulerState

-- | Remove a thread from the set of active threads. Usually called when the
--   thread is finished.
removeActiveThread :: ThreadId -> SchedulerState effs systemEvent -> SchedulerState effs systemEvent
removeActiveThread tid = over (activeThreads . mapped) (HashSet.delete tid)

-- | A suspended thread with a priority and the thread itself.
suspendThread :: Priority -> EmThread effs systemEvent -> SuspendedThread effs systemEvent
suspendThread = WithPriority

-- | Make a thread with the given priority from an action. This is a
--   convenience for defining 'SimulatorInterpreter' values.
mkThread :: Tag -> Priority -> Eff (Reader ThreadId ': Yield (EmSystemCall effs systemEvent) (Maybe systemEvent) ': effs) () -> ThreadId -> SuspendedThread effs systemEvent
mkThread tag prio action tid =
    let action' = runReader tid action
    in WithPriority
            { _priority = prio
            , _thread = EmThread
                { _threadId = tid
                , _continuation = \_ -> runC action'
                , _tag      = tag
                }
            }

-- | Make a system call
mkSysCall :: forall effs systemEvent effs2.
    Member (Yield (EmSystemCall effs systemEvent) (Maybe systemEvent)) effs2
    => Priority -- ^ The 'Priority' of the caller
    -> SysCall effs systemEvent -- ^ The system call
    -> Eff effs2 (Maybe systemEvent)
mkSysCall prio sc = yield @(EmSystemCall effs systemEvent) @(Maybe systemEvent) (WithPriority prio sc) id

-- | Start a new thread
fork :: forall effs systemEvent effs2.
    Member (Yield (EmSystemCall effs systemEvent) (Maybe systemEvent)) effs2
    => Tag -- ^ Tag of the new thread. See note [Thread Tag]
    -> Priority -- ^ Priority of the new thread.
    -> Eff (Reader ThreadId ': Yield (EmSystemCall effs systemEvent) (Maybe systemEvent) ': effs) ()
    -> Eff effs2 (Maybe systemEvent)
fork tag prio action = mkSysCall prio (Right $ Fork $ mkThread tag prio action)

-- | Suspend the current thread
sleep :: forall effs systemEvent effs2.
    Member (Yield (EmSystemCall effs systemEvent) (Maybe systemEvent)) effs2
    => Priority
    -> Eff effs2 (Maybe systemEvent)
sleep prio = mkSysCall @effs @systemEvent @effs2 prio (Left WaitForMessage)

-- | Stop the scheduler.
exit :: forall effs systemEvent effs2.
    Member (Yield (EmSystemCall effs systemEvent) (Maybe systemEvent)) effs2
    => Eff effs2 (Maybe systemEvent)
exit = mkSysCall @effs @systemEvent @effs2 Normal (Right Exit)

-- | Tag of the initial thread.
initialThreadTag :: Tag
initialThreadTag = "initial thread"

-- | Handle the 'Yield (EmSystemCall effs systemEvent) (Maybe systemEvent)'
--   effect using the scheduler, see note [Scheduler]. 'runThreads' only
--   returns when all threads are finished.
runThreads ::
    forall effs systemEvent.
    ( Eq systemEvent
    , Member (LogMsg SchedulerLog) effs
    )
    => Eff (Reader ThreadId ': Yield (EmSystemCall effs systemEvent) (Maybe systemEvent) ': effs) ()
    -> Eff effs ()
runThreads e = do
    k <- runC $ runReader initialThreadId e
    case k of
        Done () -> pure ()
        Continue _ k' ->
            let initialThread = EmThread{_continuation = k', _threadId = initialThreadId, _tag = initialThreadTag}
            in loop
                $ initialState
                    & activeThreads . at initialThreadTag . non mempty %~ HashSet.insert initialThreadId
                    & mailboxes . at initialThreadId .~ Just Seq.empty
                    & (fst . nextThreadId)
                    & enqueue (suspendThread Normal initialThread)

-- | Run the threads that are scheduled in a 'SchedulerState' to completion.
loop :: forall effs systemEvent.
    ( Eq systemEvent
    , Member (LogMsg SchedulerLog) effs
    )
    => SchedulerState effs systemEvent
    -> Eff effs ()
loop s = do
    case dequeue s of
        AThread EmThread{_continuation, _threadId, _tag} event schedulerState prio -> do
            let mkLog e = SchedulerLog{slEvent=e, slThread=_threadId, slPrio=prio, slTag = _tag}
            logDebug (mkLog Resumed)
            result <- _continuation event
            case result of
                Done () -> do
                    logDebug (mkLog $ Stopped ThreadDone)
                    loop $ schedulerState & removeActiveThread _threadId
                Continue WithPriority{_priority, _thread=sysCall} k -> do
                    logDebug SchedulerLog{slEvent=Suspended, slThread=_threadId, slPrio=_priority, slTag = _tag}
                    let thisThread = suspendThread _priority EmThread{_threadId=_threadId, _continuation=k, _tag = _tag}
                    newState <- schedulerState & enqueue thisThread & handleSysCall sysCall
                    case newState of
                        Left r -> do
                            logDebug (mkLog $ Stopped r)
                        Right newState' -> loop newState'
        _ -> pure ()

-- | Deal with a system call from a running thread.
handleSysCall ::
    ( Eq systemEvent
    , Member (LogMsg SchedulerLog) effs
    )
    => SysCall effs systemEvent
    -> SchedulerState effs systemEvent
    -> Eff effs (Either StopReason (SchedulerState effs systemEvent))
handleSysCall sysCall schedulerState = case sysCall of
    Right (Fork newThread) -> do
        let (schedulerState', tid) = nextThreadId schedulerState
            t = newThread tid
            tag = _tag $ _thread t
            newState = enqueue t schedulerState'
                        & activeThreads . at tag . non mempty %~ HashSet.insert tid
                        & mailboxes . at tid .~ Just Seq.empty
        logDebug $ SchedulerLog{slEvent = Started, slThread = tid, slPrio = _priority t, slTag = tag}
        pure (Right newState)
    Left WaitForMessage -> pure $ Right schedulerState
    Left (Broadcast msg) -> pure $ Right $ schedulerState & mailboxes . traversed %~ (|> msg)
    Left (Message t msg) -> pure $ Right $ schedulerState & mailboxes . at t . non mempty %~ (|> msg)
    Right (Thaw tid) -> do
        let (thawed, rest) = Seq.partition (\EmThread{_threadId} -> _threadId == tid) (schedulerState ^. frozen)
        pure $
            Right $
            schedulerState
                & frozen .~ rest
                & normalPrio <>~ thawed
    Right Exit -> pure (Left ThreadExit)


-- | Return a fresh thread ID and increment the counter
nextThreadId :: SchedulerState effs systemEvent -> (SchedulerState effs systemEvent, ThreadId)
nextThreadId s = (s & lastThreadId %~ ThreadId . succ . unThreadId, s ^. lastThreadId)

-- | State of the scheduler before any threads are run.
initialState :: SchedulerState effs systemEvent
initialState = SchedulerState Seq.empty Seq.empty Seq.empty initialThreadId HashMap.empty Map.empty

-- | Add a suspended thread to the queue.
enqueue :: SuspendedThread effs systemEvent -> SchedulerState effs systemEvent -> SchedulerState effs systemEvent
enqueue WithPriority {_priority, _thread} s =
    case _priority of
        Normal   -> s & normalPrio %~ (|> _thread)
        Sleeping -> s & sleeping %~ (|> _thread)
        Frozen   -> s & frozen %~ (|> _thread)

-- | Result of calling 'dequeue'. Either a thread that is ready to receive a
--   message, or no more threads.
data SchedulerDQResult effs systemEvent
    = AThread (EmThread effs systemEvent) (Maybe systemEvent) (SchedulerState effs systemEvent) Priority
    | NoMoreThreads

dequeue :: SchedulerState effs systemEvent -> SchedulerDQResult effs systemEvent
dequeue s = case dequeueThread s of
    Nothing -> NoMoreThreads
    Just (s', thread, prio) -> case dequeueMessage s' (_threadId thread) of
        Nothing       -> AThread thread Nothing s' prio
        Just (s'', m) -> AThread thread (Just m) s'' prio

-- | Find the next thread that is ready to be resumed.
--   See note [Thread Priority]
dequeueThread :: SchedulerState effs systemEvent -> Maybe (SchedulerState effs systemEvent, EmThread effs systemEvent, Priority)
dequeueThread s =
    case s ^. normalPrio of
        x :<| xs -> Just (s & normalPrio .~ xs, x, Normal)
        Empty -> case s ^. sleeping of
                x :<| xs -> Just (s & sleeping .~ xs, x, Sleeping)
                Empty    -> Nothing

-- | Get the first message for the thread.
dequeueMessage :: SchedulerState effs systemEvent -> ThreadId -> Maybe (SchedulerState effs systemEvent, systemEvent)
dequeueMessage s i = do
    mailbox <- s ^. mailboxes . at i
    (x, xs) <- case mailbox of { Empty -> Nothing; x :<| xs -> Just (x, xs) }
    pure (s & mailboxes . at i .~ Just xs, x)

---
--- Logging etc.
---

data StopReason
        = ThreadDone -- ^ The thread was done.
        | ThreadExit -- ^ The thread made the 'Exit' system call.
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)
    deriving Pretty via (PrettyShow StopReason)


data ThreadEvent = Stopped StopReason | Resumed | Suspended | Started | Thawed
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)
    deriving Pretty via (PrettyShow ThreadEvent)

data SchedulerLog =
    SchedulerLog
        { slEvent  :: ThreadEvent
        , slThread :: ThreadId
        , slTag    :: Tag
        , slPrio   :: Priority
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty SchedulerLog where
    pretty SchedulerLog{slEvent, slThread, slTag, slPrio} =
        pretty slThread <+> pretty slTag <> colon <+> pretty slEvent <+> parens (pretty slPrio)
