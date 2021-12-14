{-# LANGUAGE CPP #-}
module Foundation.Time.Bindings
    ( measuringNanoSeconds
    , getMonotonicTime
    ) where

import Basement.Imports
import Basement.Types.OffsetSize
import Basement.Types.Ptr
import Foundation.System.Bindings.Time
import Foundation.Time.Types
import Foundation.Foreign.Alloc
import Foreign.Storable

measuringNanoSeconds :: IO a -> IO (a, NanoSeconds)
measuringNanoSeconds f =
    allocaBytes (sizeOfCSize size_CTimeSpec) $ \t1 ->
    allocaBytes (sizeOfCSize size_CTimeSpec) $ \t2 -> do
        _err1 <- sysTimeClockGetTime sysTime_CLOCK_MONOTONIC t1
        r <- f
        _err2 <- sysTimeClockGetTime sysTime_CLOCK_MONOTONIC t2
        return (r, NanoSeconds 0)

getMonotonicTime :: IO (Seconds, NanoSeconds)
getMonotonicTime =
    allocaBytes (sizeOfCSize size_CTimeSpec) $ \tspec -> do
        _err1 <- sysTimeClockGetTime sysTime_CLOCK_MONOTONIC tspec
        s  <- Seconds     <$> peek (castPtr (tspec `ptrPlus` ofs_CTimeSpec_Seconds))
        ns <- NanoSeconds <$> peek (castPtr (tspec `ptrPlus` ofs_CTimeSpec_NanoSeconds))
        return (s,ns)
