-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Concurrent.Chan
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  stable
-- Portability :  non-portable (concurrency)
--
-- Unbounded channels.
--
-- The channels are implemented with 'Control.Concurrent.MVar's and therefore inherit all the
-- caveats that apply to @MVar@s (possibility of races, deadlocks etc). The
-- @stm@ (software transactional memory) library has a more robust implementation
-- of channels called @TChan@s.
--
-----------------------------------------------------------------------------

module Control.Concurrent.Chan
  (
          -- * The 'Chan' type
        Chan,                   -- abstract

          -- * Operations
        newChan,
        writeChan,
        readChan,
        dupChan,

          -- * Stream interface
        getChanContents,
        writeList2Chan,
   ) where

import Control.Concurrent.MVar
import Control.Exception (mask_)
import System.IO.Unsafe (unsafeInterleaveIO)

-- A channel is represented by two @MVar@s keeping track of the two ends
-- of the channel contents, i.e., the read- and write ends. Empty @MVar@s
-- are used to handle consumers trying to read from an empty channel.

-- |'Chan' is an abstract type representing an unbounded FIFO channel.
data Chan a
 = Chan !(MVar (Stream a))
        !(MVar (Stream a)) -- Invariant: the Stream a is always an empty MVar
   deriving Eq -- ^ @since 4.4.0.0

type Stream a = MVar (ChItem a)

data ChItem a = ChItem a !(Stream a)
  -- benchmarks show that unboxing the MVar here is worthwhile, because
  -- although it leads to higher allocation, the channel data takes up
  -- less space and is therefore quicker to GC.

-- See the Concurrent Haskell paper for a diagram explaining
-- how the different channel operations proceed.

-- @newChan@ sets up the read and write end of a channel by initialising
-- these two @MVar@s with an empty @MVar@.

-- |Build and return a new instance of 'Chan'.
newChan :: IO (Chan a)
newChan = do
   hole  <- newEmptyMVar
   readVar  <- newMVar hole
   writeVar <- newMVar hole
   return (Chan readVar writeVar)

-- To put an element on a channel, a new hole at the write end is created.
-- What was previously the empty @MVar@ at the back of the channel is then
-- filled in with a new stream element holding the entered value and the
-- new hole.

-- |Write a value to a 'Chan'.
writeChan :: Chan a -> a -> IO ()
writeChan (Chan _ writeVar) val = do
  new_hole <- newEmptyMVar
  mask_ $ do
    old_hole <- takeMVar writeVar
    putMVar old_hole (ChItem val new_hole)
    putMVar writeVar new_hole

-- The reason we don't simply do this:
--
--    modifyMVar_ writeVar $ \old_hole -> do
--      putMVar old_hole (ChItem val new_hole)
--      return new_hole
--
-- is because if an asynchronous exception is received after the 'putMVar'
-- completes and before modifyMVar_ installs the new value, it will set the
-- Chan's write end to a filled hole.

-- |Read the next value from the 'Chan'. Blocks when the channel is empty. Since
-- the read end of a channel is an 'MVar', this operation inherits fairness
-- guarantees of 'MVar's (e.g. threads blocked in this operation are woken up in
-- FIFO order).
--
-- Throws 'Control.Exception.BlockedIndefinitelyOnMVar' when the channel is
-- empty and no other thread holds a reference to the channel.
readChan :: Chan a -> IO a
readChan (Chan readVar _) =
  modifyMVar readVar $ \read_end -> do
    (ChItem val new_read_end) <- readMVar read_end
        -- Use readMVar here, not takeMVar,
        -- else dupChan doesn't work
    return (new_read_end, val)

-- |Duplicate a 'Chan': the duplicate channel begins empty, but data written to
-- either channel from then on will be available from both. Hence this creates
-- a kind of broadcast channel, where data written by anyone is seen by
-- everyone else.
--
-- (Note that a duplicated channel is not equal to its original.
-- So: @fmap (c /=) $ dupChan c@ returns @True@ for all @c@.)
dupChan :: Chan a -> IO (Chan a)
dupChan (Chan _ writeVar) = do
   hole       <- readMVar writeVar
   newReadVar <- newMVar hole
   return (Chan newReadVar writeVar)

-- Operators for interfacing with functional streams.

-- |Return a lazy list representing the contents of the supplied
-- 'Chan', much like 'GHC.Internal.System.IO.hGetContents'.
getChanContents :: Chan a -> IO [a]
getChanContents ch
  = unsafeInterleaveIO (do
        x  <- readChan ch
        xs <- getChanContents ch
        return (x:xs)
    )

-- |Write an entire list of items to a 'Chan'.
writeList2Chan :: Chan a -> [a] -> IO ()
writeList2Chan ch ls = mapM_ (writeChan ch) ls
