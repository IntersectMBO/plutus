{-# OPTIONS_HADDOCK hide #-}
module Foundation.System.Bindings.Macos
    where

import Basement.Compat.Base
import Basement.Compat.C.Types
import Foundation.System.Bindings.PosixDef
import Basement.Types.OffsetSize

#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <mach/mach.h>
#include <mach/mach_time.h>

sysMacos_O_SHLOCK
    , sysMacos_O_EXLOCK
    , sysMacos_O_SYMLINK
    , sysMacos_O_EVTONLY :: COpenFlags
sysMacos_O_SHLOCK   = (#const O_SHLOCK)
sysMacos_O_EXLOCK   = (#const O_EXLOCK)
sysMacos_O_SYMLINK  = (#const O_SYMLINK)
sysMacos_O_EVTONLY  = (#const O_EVTONLY)

data MachTimebaseInfo

size_MachTimebaseInfo :: CSize
size_MachTimebaseInfo = #const sizeof(mach_timebase_info_data_t)

ofs_MachTimebaseInfo_numer :: Offset Word8
ofs_MachTimebaseInfo_numer = Offset (#offset mach_timebase_info_data_t, numer)

ofs_MachTimebaseInfo_denom :: Offset Word8
ofs_MachTimebaseInfo_denom = Offset (#offset mach_timebase_info_data_t, denom)

foreign import ccall unsafe "mach_absolute_time"
    sysMacos_absolute_time :: IO Word64
foreign import ccall unsafe "mach_timebase_info"
    sysMacos_timebase_info :: Ptr MachTimebaseInfo -> IO ()
