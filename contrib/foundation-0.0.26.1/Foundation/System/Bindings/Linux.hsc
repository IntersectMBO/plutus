-----------------------------------------------------------------------------
-- |
-- Module      :  Foundation.System.Bindings.Linux
-- Copyright   :  (c) Vincent Hanquez 2014-2017
-- License     :  BSD-style
--
-- Maintainer  :  Vincent Hanquez
-- Stability   :  provisional
-- Portability :  non-portable (requires Linux)
--
-- Functions defined only for linux
--
-----------------------------------------------------------------------------
{-# OPTIONS_HADDOCK hide #-}
module Foundation.System.Bindings.Linux
   where

import Basement.Compat.Base
import Basement.Compat.C.Types
import Foundation.System.Bindings.PosixDef

#define __USE_GNU

#include <sys/types.h>
#include <sys/inotify.h>
#include <fcntl.h>

type CInotifyFlags = CInt
type CInotifyMask = CInt
type CWatchDescriptor = CInt

sysLinux_O_TMPFILE
    :: COpenFlags
#ifdef __O_TMPFILE
sysLinux_O_TMPFILE   = (#const __O_TMPFILE)
#else
sysLinux_O_TMPFILE   = 0
#endif

#ifdef IN_NONBLOCK
sysLinux_IN_NONBLOCK :: CInotifyFlags
sysLinux_IN_NONBLOCK = (#const IN_NONBLOCK)
#endif

#ifdef IN_CLOEXEC
sysLinux_IN_CLOEXEC :: CInotifyFlags
sysLinux_IN_CLOEXEC  = (#const IN_CLOEXEC)
#endif

sysLinux_IN_ACCESS
    , sysLinux_IN_ATTRIB
    , sysLinux_IN_CLOSE_WRITE
    , sysLinux_IN_CLOSE_NOWRITE
    , sysLinux_IN_CREATE
    , sysLinux_IN_DELETE
    , sysLinux_IN_DELETE_SELF
    , sysLinux_IN_MODIFY
    , sysLinux_IN_MOVE_SELF
    , sysLinux_IN_MOVED_FROM
    , sysLinux_IN_MOVED_TO :: CInotifyMask
sysLinux_IN_ACCESS = (#const IN_ACCESS)
sysLinux_IN_ATTRIB = (#const IN_ATTRIB)
sysLinux_IN_CLOSE_WRITE = (#const IN_CLOSE_WRITE)
sysLinux_IN_CLOSE_NOWRITE = (#const IN_CLOSE_NOWRITE)
sysLinux_IN_CREATE = (#const IN_CREATE)
sysLinux_IN_DELETE = (#const IN_DELETE)
sysLinux_IN_DELETE_SELF = (#const IN_DELETE_SELF)
sysLinux_IN_MODIFY = (#const IN_MODIFY)
sysLinux_IN_MOVE_SELF = (#const IN_MOVE_SELF)
sysLinux_IN_MOVED_FROM = (#const IN_MOVED_FROM)
sysLinux_IN_MOVED_TO = (#const IN_MOVED_TO)

-- extra mask at add_watch time
sysLinux_IN_OPEN
    , sysLinux_IN_DONT_FOLLOW
    , sysLinux_IN_MASK_ADD
    , sysLinux_IN_ONESHOT
    , sysLinux_IN_ONLYDIR :: CInotifyMask
sysLinux_IN_OPEN = (#const IN_OPEN)
sysLinux_IN_DONT_FOLLOW = (#const IN_DONT_FOLLOW)
sysLinux_IN_MASK_ADD = (#const IN_MASK_ADD)
sysLinux_IN_ONESHOT = (#const IN_ONESHOT)
sysLinux_IN_ONLYDIR = (#const IN_ONLYDIR)

#ifdef IN_EXCL_UNLINK
sysLinux_IN_EXCL_UNLINK :: CInotifyMask
sysLinux_IN_EXCL_UNLINK = (#const IN_EXCL_UNLINK)
#endif

-- only found in mask
sysLinux_IN_IGNORED
    , sysLinux_IN_ISDIR
    , sysLinux_IN_Q_OVERFLOW
    , sysLinux_IN_UNMOUNT :: CInotifyMask
sysLinux_IN_IGNORED = (#const IN_IGNORED)
sysLinux_IN_ISDIR = (#const IN_ISDIR)
sysLinux_IN_Q_OVERFLOW = (#const IN_Q_OVERFLOW)
sysLinux_IN_UNMOUNT = (#const IN_UNMOUNT)

cinotifyEventSize :: CSize
cinotifyEventSize = 16

foreign import ccall unsafe "inotify_init1"
    sysLinuxInotifyInit :: CInotifyFlags -> IO CFd
foreign import ccall unsafe "inotify_add_watch"
    sysLinuxInotifyAddWatch :: CFd -> Ptr CChar -> CInotifyMask -> IO CWatchDescriptor
foreign import ccall unsafe "inotify_rm_watch"
    sysLinuxInotifyRmWatch :: CFd -> CWatchDescriptor -> IO Int
