module Control.Concurrent (
  ThreadId, myThreadId,

  forkIO, forkFinally, forkIOWithUnmask,
  killThread, throwTo,

  yield,
  threadDelay,

  threadStatus,
  ThreadStatus(..),
  BlockReason(..),

  module Control.Concurrent.MVar,
  module Control.Concurrent.Chan,
  module Control.Concurrent.QSem,
  module Control.Concurrent.QSemN,

{-
  forkOn, forkOnWithUnmask, getNumCapabilities, setNumCapabilities, threadCapability,
  threadWaitRead, threadWaitWrite,
  threadWaitReadSTM, threadWaitWriteSTM,
  rtsSupportsBoundThreads,
  forkOS, forkOSWithUnmask,
  isCurrentThreadBound,
  runInBoundThread, runInUnboundThread,
  mkWeakThreadId,
-}
  ) where
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent.QSem
import Control.Concurrent.QSemN
import Control.Exception
import Control.Exception.Internal (unsafeUnmask)
import Data.Word
import Primitives

instance Show ThreadId where
  show i = "ThreadId#" ++ show (primThreadNum i)

instance Eq ThreadId where
  i == i'  =  primThreadNum i == primThreadNum i'

instance Ord ThreadId where
  i `compare` i'  =  primThreadNum i `compare` primThreadNum i'

forkIO :: IO () -> IO ThreadId
forkIO action = --primForkIO (catch action childHandler)
  primForkIO action

childHandler :: SomeException -> IO ()
childHandler err = catch (realHandler err) childHandler

realHandler :: SomeException -> IO ()
realHandler se
  | Just BlockedIndefinitelyOnMVar <- fromException se  =  return ()
--  | Just BlockedIndefinitelyOnSTM  <- fromException se  =  return ()
  | Just ThreadKilled              <- fromException se  =  return ()
  | otherwise                                           =  throw se

myThreadId :: IO ThreadId
myThreadId = primMyThreadId

forkFinally :: IO a -> (Either SomeException a -> IO ()) -> IO ThreadId
forkFinally action and_then =
  mask $ \restore ->
    forkIO $ try (restore action) >>= and_then

forkIOWithUnmask :: ((forall a . IO a -> IO a) -> IO ()) -> IO ThreadId
forkIOWithUnmask io = forkIO (io unsafeUnmask)

killThread :: ThreadId -> IO ()
killThread tid = throwTo tid ThreadKilled

primThrowTo :: ThreadId -> SomeException -> IO ()
primThrowTo = _primitive "IO.throwto"

throwTo :: Exception e => ThreadId -> e -> IO ()
throwTo thid ex = primThrowTo thid (toException ex)

yield :: IO ()
yield = primYield

threadDelay :: Int -> IO ()
threadDelay = primThreadDelay

---------------------------------------

data BlockReason
  = BlockedOnMVar
  | BlockedOnBlackHole
  | BlockedOnException
  | BlockedOnSTM
  | BlockedOnForeignCall
  | BlockedOnOther
  deriving (Eq, Ord, Show)

data ThreadStatus
  = ThreadRunning
  | ThreadFinished
  | ThreadBlocked  BlockReason
  | ThreadDied
  deriving (Eq, Ord, Show)

-- XXX Does not do BlockedOnException correctly
threadStatus :: ThreadId -> IO ThreadStatus
threadStatus thr = do
  st <- primThreadStatus thr
  return $
    case st of
      0 -> ThreadRunning                 -- ts_runnable
      1 -> ThreadBlocked BlockedOnMVar   -- ts_wait_mvar
      2 -> ThreadBlocked BlockedOnOther  -- ts_wait_time
      3 -> ThreadFinished                -- ts_finished
      4 -> ThreadDied                    -- ts_died
