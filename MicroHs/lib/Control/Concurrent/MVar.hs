module Control.Concurrent.MVar(
  MVar,
  newEmptyMVar,
  newMVar,
  takeMVar,
  putMVar,
  readMVar,
  swapMVar,
  tryTakeMVar,
  tryPutMVar,
  isEmptyMVar,
  withMVar,
  withMVarMasked,
  modifyMVar_,
  modifyMVar,
  modifyMVarMasked_,
  modifyMVarMasked,
  tryReadMVar,
  --mkWeakMVar,
  --addMVarFinalizer,
  ) where
import Primitives
import Control.Exception
import Data.Maybe(isNothing)

instance Eq (MVar a) where
  mv1 == mv2  =  primMVarToWord mv1 == primMVarToWord mv2

newEmptyMVar :: IO (MVar a)
newEmptyMVar = primNewEmptyMVar

newMVar :: a -> IO (MVar a)
newMVar value = do
    mvar <- newEmptyMVar
    putMVar mvar value
    return mvar

takeMVar :: MVar a -> IO a
takeMVar mv = primTakeMVar mv

readMVar :: MVar a -> IO a
readMVar mv = primReadMVar mv

putMVar :: MVar a -> a -> IO ()
putMVar = primPutMVar

tryTakeMVar :: MVar a -> IO (Maybe a)
tryTakeMVar = primTryTakeMVar

tryPutMVar :: MVar a -> a -> IO Bool
tryPutMVar = primTryPutMVar

tryReadMVar :: MVar a -> IO (Maybe a)
tryReadMVar = primTryReadMVar

isEmptyMVar :: MVar a -> IO Bool
isEmptyMVar mv = isNothing <$> tryReadMVar mv

swapMVar :: MVar a -> a -> IO a
swapMVar mvar new =
  mask_ $ do
    old <- takeMVar mvar
    putMVar mvar new
    return old

withMVar :: MVar a -> (a -> IO b) -> IO b
withMVar m io =
  mask $ \restore -> do
    a <- takeMVar m
    b <- restore (io a) `onException` putMVar m a
    putMVar m a
    return b

withMVarMasked :: MVar a -> (a -> IO b) -> IO b
withMVarMasked m io =
  mask_ $ do
    a <- takeMVar m
    b <- io a `onException` putMVar m a
    putMVar m a
    return b

modifyMVar_ :: MVar a -> (a -> IO a) -> IO ()
modifyMVar_ m io =
  mask $ \restore -> do
    a  <- takeMVar m
    a' <- restore (io a) `onException` putMVar m a
    putMVar m a'

modifyMVar :: MVar a -> (a -> IO (a,b)) -> IO b
modifyMVar m io =
  mask $ \restore -> do
    a      <- takeMVar m
    (a',b) <- restore (io a >>= evaluate) `onException` putMVar m a
    putMVar m a'
    return b

modifyMVarMasked_ :: MVar a -> (a -> IO a) -> IO ()
modifyMVarMasked_ m io =
  mask_ $ do
    a  <- takeMVar m
    a' <- io a `onException` putMVar m a
    putMVar m a'

modifyMVarMasked :: MVar a -> (a -> IO (a,b)) -> IO b
modifyMVarMasked m io =
  mask_ $ do
    a      <- takeMVar m
    (a',b) <- (io a >>= evaluate) `onException` putMVar m a
    putMVar m a'
    return b
