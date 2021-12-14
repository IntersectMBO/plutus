-- |
-- Module      : Foundation.Timing
-- License     : BSD-style
-- Maintainer  : Foundation maintainers
--
-- An implementation of a timing framework
--
{-# LANGUAGE CPP #-}
module Foundation.Timing
    ( Timing(..)
    , Measure(..)
    , stopWatch
    , measure
    ) where

import           Basement.Imports hiding (from)
import           Basement.From (from)
#if __GLASGOW_HASKELL__ < 802
import           Basement.Cast (cast)
#endif
import           Basement.Monad
-- import           Basement.UArray hiding (unsafeFreeze)
import           Basement.UArray.Mutable (MUArray)
import           Foundation.Collection
import           Foundation.Time.Types
import           Foundation.Numerical
import           Foundation.Time.Bindings
import           Control.Exception (evaluate)
import           System.Mem (performGC)
import           Data.Function (on)
import qualified GHC.Stats as GHC


data Timing = Timing
    { timeDiff           :: !NanoSeconds
    , timeBytesAllocated :: !(Maybe Word64)
    }

data Measure = Measure
    { measurements :: UArray NanoSeconds
    , iters        :: Word
    }

#if __GLASGOW_HASKELL__ >= 802
type GCStats = GHC.RTSStats

getGCStats :: IO (Maybe GCStats)
getGCStats = do
    r <- GHC.getRTSStatsEnabled
    if r then pure Nothing else Just <$> GHC.getRTSStats

diffGC :: Maybe GHC.RTSStats -> Maybe GHC.RTSStats -> Maybe Word64
diffGC gc2 gc1 = ((-) `on` GHC.allocated_bytes) <$> gc2 <*> gc1
#else
type GCStats = GHC.GCStats

getGCStats :: IO (Maybe GCStats)
getGCStats = do
    r <- GHC.getGCStatsEnabled
    if r then pure Nothing else Just <$> GHC.getGCStats

diffGC :: Maybe GHC.GCStats -> Maybe GHC.GCStats -> Maybe Word64
diffGC gc2 gc1 = cast <$> (((-) `on` GHC.bytesAllocated) <$> gc2 <*> gc1)
#endif

-- | Simple one-time measurement of time & other metrics spent in a function
stopWatch :: (a -> b) -> a -> IO Timing
stopWatch f !a = do
    performGC
    gc1 <- getGCStats
    (_, ns) <- measuringNanoSeconds (evaluate $ f a)
    gc2 <- getGCStats
    return $ Timing ns (diffGC gc2 gc1)

-- | In depth timing & other metrics analysis of a function
measure :: Word -> (a -> b) -> a -> IO Measure
measure nbIters f a = do
    d <- mutNew (from nbIters) :: IO (MUArray NanoSeconds (PrimState IO))
    loop d 0
    Measure <$> unsafeFreeze d
            <*> pure nbIters
  where
    loop d !i
        | i == nbIters = return ()
        | otherwise    = do
            (_, r) <- measuringNanoSeconds (evaluate $ f a)
            mutUnsafeWrite d (from i) r
            loop d (i+1)
