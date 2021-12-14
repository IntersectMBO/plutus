{-# LANGUAGE CPP #-}

module Foundation.Time.StopWatch
    ( StopWatchPrecise
    , startPrecise
    , stopPrecise
    ) where

import Basement.Imports
import Basement.Types.Ptr
import Foundation.Time.Types
import Basement.Block.Mutable
import Foundation.Numerical
import Foreign.Storable

#if defined(mingw32_HOST_OS)
import System.Win32.Time
import Basement.Monad
import Basement.IntegralConv
import System.IO.Unsafe
#elif defined(darwin_HOST_OS)
import Foundation.System.Bindings.Macos
import Basement.IntegralConv
import System.IO.Unsafe
import Basement.Types.OffsetSize
#else
import Foundation.System.Bindings.Time
import Basement.Monad
import Basement.Types.OffsetSize
#endif

-- | A precise stop watch
--
-- The precision is higher than a normal stopwatch, but
-- also on some system it might not be able to record
-- longer period of time accurately (possibly wrapping)
newtype StopWatchPrecise =
#if defined(darwin_HOST_OS)
    StopWatchPrecise Word64
#elif defined(mingw32_HOST_OS)
    -- contain 2 LARGE_INTEGER (int64_t)
    StopWatchPrecise (MutableBlock Word8 (PrimState IO))
#else
    -- contains 2 timespec (16 bytes)
    StopWatchPrecise (MutableBlock Word8 (PrimState IO))
#endif

#if defined(mingw32_HOST_OS)
initPrecise :: Word64
initPrecise = unsafePerformIO $ integralDownsize <$> queryPerformanceFrequency
{-# NOINLINE initPrecise #-}
#elif defined(darwin_HOST_OS)
initPrecise :: (Word64, Word64)
initPrecise = unsafePerformIO $ do
    mti <- newPinned (sizeOfCSize size_MachTimebaseInfo)
    withMutablePtr mti $ \p -> do
        sysMacos_timebase_info (castPtr p)
        let p32 = castPtr p :: Ptr Word32
        !n <- peek (p32 `ptrPlus` ofs_MachTimebaseInfo_numer)
        !d <- peek (p32 `ptrPlus` ofs_MachTimebaseInfo_denom)
        pure (integralUpsize n, integralUpsize d)
{-# NOINLINE initPrecise #-}
#endif

-- | Create a new precise stop watch
--
-- record the time at start of call
startPrecise :: IO StopWatchPrecise
startPrecise = do
#if defined(mingw32_HOST_OS)
    blk <- newPinned 16
    _ <- withMutablePtr blk $ \p ->
        c_QueryPerformanceCounter (castPtr p `ptrPlus` 8)
    pure (StopWatchPrecise blk)
#elif defined(darwin_HOST_OS)
    StopWatchPrecise <$> sysMacos_absolute_time
#else
    blk <- newPinned (sizeOfCSize (size_CTimeSpec + size_CTimeSpec))
    _err1 <- withMutablePtr blk $ \p -> do
        sysTimeClockGetTime sysTime_CLOCK_MONOTONIC (castPtr p `ptrPlusCSz` size_CTimeSpec)
    pure (StopWatchPrecise blk)
#endif

-- | Get the number of nano seconds since the call to `startPrecise`
stopPrecise :: StopWatchPrecise -> IO NanoSeconds
stopPrecise (StopWatchPrecise blk) = do
#if defined(mingw32_HOST_OS)
    withMutablePtr blk $ \p -> do
        _ <- c_QueryPerformanceCounter (castPtr p)
        let p64 = castPtr p :: Ptr Word64
        end   <- peek p64
        start <- peek (p64 `ptrPlus` 8)
        pure $ NanoSeconds ((end - start) * secondInNano `div` initPrecise)
#elif defined(darwin_HOST_OS)
    end <- sysMacos_absolute_time
    pure $ NanoSeconds $ case initPrecise of
        (1,1)         -> end - blk
        (numer,denom) -> ((end - blk) * numer) `div` denom
#else
    withMutablePtr blk $ \p -> do
        _err1 <- sysTimeClockGetTime sysTime_CLOCK_MONOTONIC (castPtr p)
        let p64 = castPtr p :: Ptr Word64
        endSec    <- peek p64
        startSec  <- peek (p64 `ptrPlusCSz` size_CTimeSpec)
        endNSec   <- peek (p64 `ptrPlus` ofs_CTimeSpec_NanoSeconds)
        startNSec <- peek (p64 `ptrPlus` (sizeAsOffset (sizeOfCSize size_CTimeSpec) + ofs_CTimeSpec_NanoSeconds))
        pure $ NanoSeconds $ (endSec * secondInNano + endNSec) - (startSec * secondInNano + startNSec)
#endif

#if !defined(darwin_HOST_OS)
secondInNano :: Word64
secondInNano = 1000000000
#endif
