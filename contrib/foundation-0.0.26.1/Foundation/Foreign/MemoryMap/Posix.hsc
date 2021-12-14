-----------------------------------------------------------------------------
-- |
-- Module      :  Foundation.Foreign.MemoryMap.Posix
-- Copyright   :  (c) Vincent Hanquez 2014
-- License     :  BSD-style
--
-- Maintainer  :  Vincent Hanquez
-- Stability   :  provisional
-- Portability :  non-portable (requires POSIX)
--
-- Functions defined by the POSIX standards for manipulating memory maps
--
-- When a function that calls an underlying POSIX function fails, the errno
-- code is converted to an 'IOError' using 'Foreign.C.Error.errnoToIOError'.
-- For a list of which errno codes may be generated, consult the POSIX
-- documentation for the underlying function.
--
-----------------------------------------------------------------------------

#include <sys/mman.h>
#include <unistd.h>

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CPP #-}
module Foundation.Foreign.MemoryMap.Posix
    ( memoryMap
    , memoryUnmap
    , memoryAdvise
    , memoryLock
    , memoryUnlock
    , memoryProtect
    , memorySync
    -- * Flags types
    , MemoryMapFlag(..)
    , MemoryProtection(..)
    , MemoryAdvice(..)
    , MemorySyncFlag(..)
    -- * system page size
    , sysconfPageSize
    -- * High level
    , fileMapRead
    ) where

import Basement.Compat.Base
import Basement.Compat.C.Types
import Basement.Types.OffsetSize
import System.Posix.Types
import Foreign.Ptr
import Foreign.C.Error
import Data.Bits

import Foundation.Collection.Foldable
import Foundation.VFS
import qualified Prelude (fromIntegral)
import Foundation.Foreign.MemoryMap.Types
import Control.Exception

import           GHC.IO.FD
import           GHC.IO.IOMode
import qualified GHC.IO.Device as IO

foreign import ccall unsafe "mmap"
    c_mmap :: Ptr a -> CSize -> CInt -> CInt -> CInt -> COff -> IO (Ptr a)

foreign import ccall unsafe "munmap"
    c_munmap :: Ptr a -> CSize -> IO CInt

#if defined(POSIX_MADV_NORMAL)
foreign import ccall unsafe "posix_madvise"
    c_madvise :: Ptr a -> CSize -> CInt -> IO CInt
#else
foreign import ccall unsafe "madvise"
    c_madvise :: Ptr a -> CSize -> CInt -> IO CInt
#endif

foreign import ccall unsafe "msync"
    c_msync :: Ptr a -> CSize -> CInt -> IO CInt

foreign import ccall unsafe "mprotect"
    c_mprotect :: Ptr a -> CSize -> CInt -> IO CInt

#ifndef __HAIKU__
foreign import ccall unsafe "mlock"
    c_mlock :: Ptr a -> CSize -> IO CInt
#else
c_mlock :: Ptr a -> CSize -> IO CInt
c_mlock _ _ = return (-1)
#endif

#ifndef __HAIKU__
foreign import ccall unsafe "munlock"
    c_munlock :: Ptr a -> CSize -> IO CInt
#else
c_munlock :: Ptr a -> CSize -> IO CInt
c_munlock _ _ = return (-1)
#endif

foreign import ccall unsafe "sysconf"
    c_sysconf :: CInt -> CLong

-- | Mapping flag
data MemoryMapFlag =
      MemoryMapShared  -- ^ memory changes are shared between process
    | MemoryMapPrivate -- ^ memory changes are private to process
    deriving (Show,Eq)

-- | Memory protection
data MemoryProtection =
      MemoryProtectionNone
    | MemoryProtectionRead
    | MemoryProtectionWrite
    | MemoryProtectionExecute
    deriving (Show,Eq)

-- | Advice to put on memory.
--
-- only define the posix one.
data MemoryAdvice =
      MemoryAdviceNormal     -- ^ no specific advice, the default.
    | MemoryAdviceRandom     -- ^ Expect page references in random order. No readahead should occur.
    | MemoryAdviceSequential -- ^ Expect page references in sequential order. Page should be readahead aggressively.
    | MemoryAdviceWillNeed   -- ^ Expect access in the near future. Probably a good idea to readahead early
    | MemoryAdviceDontNeed   -- ^ Do not expect access in the near future.
    deriving (Show,Eq)

-- | Memory synchronization flags
data MemorySyncFlag =
      MemorySyncAsync      -- ^ perform asynchronous write.
    | MemorySyncSync       -- ^ perform synchronous write.
    | MemorySyncInvalidate -- ^ invalidate cache data.
    deriving (Show,Eq)

cvalueOfMemoryProts :: [MemoryProtection] -> CInt
cvalueOfMemoryProts = foldl' (.|.) 0 . fmap toProt
  where toProt :: MemoryProtection -> CInt
        toProt MemoryProtectionNone    = (#const PROT_NONE)
        toProt MemoryProtectionRead    = (#const PROT_READ)
        toProt MemoryProtectionWrite   = (#const PROT_WRITE)
        toProt MemoryProtectionExecute = (#const PROT_EXEC)

cvalueOfMemorySync :: [MemorySyncFlag] -> CInt
cvalueOfMemorySync = foldl' (.|.) 0 . fmap toSync
  where toSync MemorySyncAsync      = (#const MS_ASYNC)
        toSync MemorySyncSync       = (#const MS_SYNC)
        toSync MemorySyncInvalidate = (#const MS_INVALIDATE)

-- | Map pages of memory.
--
-- If fd is present, this memory will represent the file associated.
-- Otherwise, the memory will be an anonymous mapping.
--
-- use 'mmap'
memoryMap :: Maybe (Ptr a)      -- ^ The address to map to if MapFixed is used.
          -> CSize              -- ^ The length of the mapping
          -> [MemoryProtection] -- ^ the memory protection associated with the mapping
          -> MemoryMapFlag      -- ^
          -> Maybe Fd
          -> COff
          -> IO (Ptr a)
memoryMap initPtr sz prots flag mfd off =
    throwErrnoIf (== m1ptr) "mmap" (c_mmap (maybe nullPtr id initPtr) sz cprot cflags fd off)
  where m1ptr  = nullPtr `plusPtr` (-1)
        fd     = maybe (-1) (\(Fd v) -> v) mfd
        cprot  = cvalueOfMemoryProts prots
        cflags = maybe cMapAnon (const 0) mfd
             .|. maybe 0 (const cMapFixed) initPtr
             .|. toMapFlag flag

#ifdef __APPLE__
        cMapAnon  = (#const MAP_ANON)
#else
        cMapAnon  = (#const MAP_ANONYMOUS)
#endif
        cMapFixed = (#const MAP_FIXED)

        toMapFlag MemoryMapShared  = (#const MAP_SHARED)
        toMapFlag MemoryMapPrivate = (#const MAP_PRIVATE)

-- | Unmap pages of memory
--
-- use 'munmap'
memoryUnmap :: Ptr a -> CSize -> IO ()
memoryUnmap ptr sz = throwErrnoIfMinus1_ "munmap" (c_munmap ptr sz)

-- | give advice to the operating system about use of memory
--
-- call 'madvise'
memoryAdvise :: Ptr a -> CSize -> MemoryAdvice -> IO ()
memoryAdvise ptr sz adv = throwErrnoIfMinus1_ "madvise" (c_madvise ptr sz cadv)
  where cadv = toAdvice adv
#if defined(POSIX_MADV_NORMAL)
        toAdvice MemoryAdviceNormal = (#const POSIX_MADV_NORMAL)
        toAdvice MemoryAdviceRandom = (#const POSIX_MADV_RANDOM)
        toAdvice MemoryAdviceSequential = (#const POSIX_MADV_SEQUENTIAL)
        toAdvice MemoryAdviceWillNeed = (#const POSIX_MADV_WILLNEED)
        toAdvice MemoryAdviceDontNeed = (#const POSIX_MADV_DONTNEED)
#else
        toAdvice MemoryAdviceNormal = (#const MADV_NORMAL)
        toAdvice MemoryAdviceRandom = (#const MADV_RANDOM)
        toAdvice MemoryAdviceSequential = (#const MADV_SEQUENTIAL)
        toAdvice MemoryAdviceWillNeed = (#const MADV_WILLNEED)
        toAdvice MemoryAdviceDontNeed = (#const MADV_DONTNEED)
#endif

-- | lock a range of process address space
--
-- call 'mlock'
memoryLock :: Ptr a -> CSize -> IO ()
memoryLock ptr sz = throwErrnoIfMinus1_ "mlock" (c_mlock ptr sz)

-- | unlock a range of process address space
--
-- call 'munlock'
memoryUnlock :: Ptr a -> CSize -> IO ()
memoryUnlock ptr sz = throwErrnoIfMinus1_ "munlock" (c_munlock ptr sz)

-- | set protection of memory mapping
--
-- call 'mprotect'
memoryProtect :: Ptr a -> CSize -> [MemoryProtection] -> IO ()
memoryProtect ptr sz prots = throwErrnoIfMinus1_ "mprotect" (c_mprotect ptr sz cprot)
  where cprot = cvalueOfMemoryProts prots

-- | memorySync synchronize memory with physical storage.
--
-- On an anonymous mapping this function does not have any effect.
-- call 'msync'
memorySync :: Ptr a -> CSize -> [MemorySyncFlag] -> IO ()
memorySync ptr sz flags = throwErrnoIfMinus1_ "msync" (c_msync ptr sz cflags)
  where cflags = cvalueOfMemorySync flags

-- | Return the operating system page size.
--
-- call 'sysconf'
sysconfPageSize :: Int
sysconfPageSize = Prelude.fromIntegral $ c_sysconf (#const _SC_PAGESIZE)

--------------------------------------------------------------------------------

fileSizeToCSize :: FileSize -> CSize
fileSizeToCSize (FileSize sz) = Prelude.fromIntegral sz

fileSizeFromInteger :: Integer -> FileSize
fileSizeFromInteger = FileSize . Prelude.fromIntegral

fileMapRead :: FileMapReadF
fileMapRead fp = bracket (openFile (filePathToLString fp) ReadMode True) (IO.close . fst) $ \(fd,_) -> do
    sz   <- fileSizeFromInteger `fmap` IO.getSize fd
    let csz = fileSizeToCSize sz
    p    <- memoryMap Nothing csz [MemoryProtectionRead] MemoryMapPrivate (Just $ Fd $ fdFD fd) 0
    return $ FileMapping p sz (memoryUnmap p csz)
