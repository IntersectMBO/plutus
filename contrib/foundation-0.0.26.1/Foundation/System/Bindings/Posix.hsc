-----------------------------------------------------------------------------
-- |
-- Module      :  Foundation.System.Bindings.Posix
-- Copyright   :  (c) Vincent Hanquez 2014-2017
-- License     :  BSD-style
--
-- Maintainer  :  Vincent Hanquez
-- Stability   :  provisional
-- Portability :  non-portable (requires POSIX)
--
-- Functions defined by the POSIX standards
--
-----------------------------------------------------------------------------
{-# LANGUAGE CApiFFI #-}
{-# OPTIONS_HADDOCK hide #-}
module Foundation.System.Bindings.Posix
   where

import Basement.Compat.Base
import Basement.Compat.C.Types
import Data.Bits
import Foundation.System.Bindings.PosixDef

#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

data CDir
data CDirent

sysPosix_E2BIG
    , sysPosix_EACCES
    , sysPosix_EADDRINUSE
    , sysPosix_EADDRNOTAVAIL
    , sysPosix_EAFNOSUPPORT
    , sysPosix_EAGAIN
    , sysPosix_EALREADY
    , sysPosix_EBADF
    , sysPosix_EBUSY
    , sysPosix_ECANCELED
    , sysPosix_ECHILD
    , sysPosix_ECONNABORTED
    , sysPosix_ECONNREFUSED
    , sysPosix_ECONNRESET
    , sysPosix_EDEADLK
    , sysPosix_EDESTADDRREQ
    , sysPosix_EDOM
    , sysPosix_EDQUOT
    , sysPosix_EEXIST
    , sysPosix_EFAULT
    , sysPosix_EFBIG
    , sysPosix_EHOSTUNREACH
    , sysPosix_EIDRM
    , sysPosix_EILSEQ
    , sysPosix_EINPROGRESS
    , sysPosix_EINTR
    , sysPosix_EINVAL
    , sysPosix_EIO
    , sysPosix_EISCONN
    , sysPosix_EISDIR
    , sysPosix_ELOOP
    , sysPosix_EMFILE
    , sysPosix_EMLINK
    , sysPosix_EMSGSIZE
    , sysPosix_ENAMETOOLONG
    , sysPosix_ENETDOWN
    , sysPosix_ENETRESET
    , sysPosix_ENETUNREACH
    , sysPosix_ENFILE
    , sysPosix_ENOBUFS
    , sysPosix_ENODEV
    , sysPosix_ENOENT
    , sysPosix_ENOEXEC
    , sysPosix_ENOLCK
    , sysPosix_ENOMEM
    , sysPosix_ENOMSG
    , sysPosix_ENOPROTOOPT
    , sysPosix_ENOSPC
    , sysPosix_ENOSYS
    , sysPosix_ENOTCONN
    , sysPosix_ENOTDIR
    , sysPosix_ENOTEMPTY
    , sysPosix_ENOTSOCK
    , sysPosix_ENOTSUP
    , sysPosix_ENOTTY
    , sysPosix_ENXIO
    , sysPosix_EOPNOTSUPP
    , sysPosix_EOVERFLOW
    , sysPosix_EPERM
    , sysPosix_EPIPE
    , sysPosix_EPROTONOSUPPORT
    , sysPosix_EPROTOTYPE
    , sysPosix_ERANGE
    , sysPosix_EROFS
    , sysPosix_ESPIPE
    , sysPosix_ESRCH
    , sysPosix_ESTALE
    , sysPosix_ETIMEDOUT
    , sysPosix_ETXTBSY
    , sysPosix_EWOULDBLOCK
    , sysPosix_EXDEV :: CErrno
sysPosix_E2BIG = (#const E2BIG)
sysPosix_EACCES = (#const EACCES)
sysPosix_EADDRINUSE = (#const EADDRINUSE)
sysPosix_EADDRNOTAVAIL = (#const EADDRNOTAVAIL)
sysPosix_EAFNOSUPPORT = (#const EAFNOSUPPORT)
sysPosix_EAGAIN = (#const EAGAIN)
sysPosix_EALREADY = (#const EALREADY)
sysPosix_EBADF = (#const EBADF)
sysPosix_EBUSY = (#const EBUSY)
sysPosix_ECANCELED = (#const ECANCELED)
sysPosix_ECHILD = (#const ECHILD)
sysPosix_ECONNABORTED = (#const ECONNABORTED)
sysPosix_ECONNREFUSED = (#const ECONNREFUSED)
sysPosix_ECONNRESET = (#const ECONNRESET)
sysPosix_EDEADLK = (#const EDEADLK)
sysPosix_EDESTADDRREQ = (#const EDESTADDRREQ)
sysPosix_EDOM = (#const EDOM)
sysPosix_EDQUOT = (#const EDQUOT)
sysPosix_EEXIST = (#const EEXIST)
sysPosix_EFAULT = (#const EFAULT)
sysPosix_EFBIG = (#const EFBIG)
sysPosix_EHOSTUNREACH = (#const EHOSTUNREACH)
sysPosix_EIDRM = (#const EIDRM)
sysPosix_EILSEQ = (#const EILSEQ)
sysPosix_EINPROGRESS = (#const EINPROGRESS)
sysPosix_EINTR = (#const EINTR)
sysPosix_EINVAL = (#const EINVAL)
sysPosix_EIO = (#const EIO)
sysPosix_EISCONN = (#const EISCONN)
sysPosix_EISDIR = (#const EISDIR)
sysPosix_ELOOP = (#const ELOOP)
sysPosix_EMFILE = (#const EMFILE)
sysPosix_EMLINK = (#const EMLINK)
sysPosix_EMSGSIZE = (#const EMSGSIZE)
sysPosix_ENAMETOOLONG = (#const ENAMETOOLONG)
sysPosix_ENETDOWN = (#const ENETDOWN)
sysPosix_ENETRESET = (#const ENETRESET)
sysPosix_ENETUNREACH = (#const ENETUNREACH)
sysPosix_ENFILE = (#const ENFILE)
sysPosix_ENOBUFS = (#const ENOBUFS)
sysPosix_ENODEV = (#const ENODEV)
sysPosix_ENOENT = (#const ENOENT)
sysPosix_ENOEXEC = (#const ENOEXEC)
sysPosix_ENOLCK = (#const ENOLCK)
sysPosix_ENOMEM = (#const ENOMEM)
sysPosix_ENOMSG = (#const ENOMSG)
sysPosix_ENOPROTOOPT = (#const ENOPROTOOPT)
sysPosix_ENOSPC = (#const ENOSPC)
sysPosix_ENOSYS = (#const ENOSYS)
sysPosix_ENOTCONN = (#const ENOTCONN)
sysPosix_ENOTDIR = (#const ENOTDIR)
sysPosix_ENOTEMPTY = (#const ENOTEMPTY)
sysPosix_ENOTSOCK = (#const ENOTSOCK)
sysPosix_ENOTSUP = (#const ENOTSUP)
sysPosix_ENOTTY = (#const ENOTTY)
sysPosix_ENXIO = (#const ENXIO)
sysPosix_EOPNOTSUPP = (#const EOPNOTSUPP)
sysPosix_EOVERFLOW = (#const EOVERFLOW)
sysPosix_EPERM = (#const EPERM)
sysPosix_EPIPE = (#const EPIPE)
sysPosix_EPROTONOSUPPORT = (#const EPROTONOSUPPORT)
sysPosix_EPROTOTYPE = (#const EPROTOTYPE)
sysPosix_ERANGE = (#const ERANGE)
sysPosix_EROFS = (#const EROFS)
sysPosix_ESPIPE = (#const ESPIPE)
sysPosix_ESRCH = (#const ESRCH)
sysPosix_ESTALE = (#const ESTALE)
sysPosix_ETIMEDOUT = (#const ETIMEDOUT)
sysPosix_ETXTBSY = (#const ETXTBSY)
sysPosix_EWOULDBLOCK = (#const EWOULDBLOCK)
sysPosix_EXDEV = (#const EXDEV)

#ifdef ENODATA
sysPosix_ENODATA :: CErrno
sysPosix_ENODATA = (#const ENODATA)
#endif

#ifdef ENOSR
sysPosix_ENOSR :: CErrno
sysPosix_ENOSR = (#const ENOSR)
#endif

#ifdef ENOSTR
sysPosix_ENOSTR :: CErrno
sysPosix_ENOSTR = (#const ENOSTR)
#endif

#ifdef ETIME
sysPosix_ETIME :: CErrno
sysPosix_ETIME = (#const ETIME)
#endif

#ifdef EBADMSG
sysPosix_EBADMSG :: CErrno
sysPosix_EBADMSG = (#const EBADMSG)
#endif

#ifdef EMULTIHOP
sysPosix_EMULTIHOP :: CErrno
sysPosix_EMULTIHOP = (#const EMULTIHOP)
#endif

#ifdef ENOLINK
sysPosix_ENOLINK :: CErrno
sysPosix_ENOLINK = (#const ENOLINK)
#endif

#ifdef ENOTRECOVERABLE
sysPosix_ENOTRECOVERABLE :: CErrno
sysPosix_ENOTRECOVERABLE = (#const ENOTRECOVERABLE)
#endif

#ifdef EOWNERDEAD
sysPosix_EOWNERDEAD :: CErrno
sysPosix_EOWNERDEAD = (#const EOWNERDEAD)
#endif

#ifdef EPROTO
sysPosix_EPROTO :: CErrno
sysPosix_EPROTO = (#const EPROTO)
#endif

sysPosix_O_RDONLY
    , sysPosix_O_WRONLY
    , sysPosix_O_RDWR
    , sysPosix_O_NONBLOCK
    , sysPosix_O_APPEND
    , sysPosix_O_CREAT
    , sysPosix_O_TRUNC
    , sysPosix_O_EXCL :: COpenFlags
sysPosix_O_RDONLY   = (#const O_RDONLY)
sysPosix_O_WRONLY   = (#const O_WRONLY)
sysPosix_O_RDWR     = ((#const O_RDONLY) .|. (#const O_WRONLY))
sysPosix_O_NONBLOCK = (#const O_NONBLOCK)
sysPosix_O_APPEND   = (#const O_APPEND)
sysPosix_O_CREAT    = (#const O_CREAT)
sysPosix_O_TRUNC    = (#const O_TRUNC)
sysPosix_O_EXCL     = (#const O_EXCL)

#ifdef O_NOFOLLOW
sysPosix_O_NOFOLLOW :: COpenFlags
sysPosix_O_NOFOLLOW = (#const O_NOFOLLOW)
#endif

#ifdef O_CLOEXEC
sysPosix_O_CLOEXEC :: COpenFlags
sysPosix_O_CLOEXEC  = (#const O_CLOEXEC)
#endif

sysPosix_PROT_NONE
    , sysPosix_PROT_READ
    , sysPosix_PROT_WRITE
    , sysPosix_PROT_EXEC :: CMemProtFlags
sysPosix_PROT_NONE  = (#const PROT_NONE)
sysPosix_PROT_READ  = (#const PROT_READ)
sysPosix_PROT_WRITE = (#const PROT_WRITE)
sysPosix_PROT_EXEC  = (#const PROT_EXEC)

sysPosix_MAP_SHARED
    , sysPosix_MAP_PRIVATE
    , sysPosix_MAP_FIXED
    , sysPosix_MAP_ANONYMOUS :: CMemMappingFlags
sysPosix_MAP_SHARED    = (#const MAP_SHARED)
sysPosix_MAP_PRIVATE   = (#const MAP_PRIVATE)
sysPosix_MAP_FIXED     = (#const MAP_FIXED)
#ifdef __APPLE__
sysPosix_MAP_ANONYMOUS = (#const MAP_ANON)
#else
sysPosix_MAP_ANONYMOUS = (#const MAP_ANONYMOUS)
#endif

sysPosix_MADV_NORMAL
    , sysPosix_MADV_RANDOM
    , sysPosix_MADV_SEQUENTIAL
    , sysPosix_MADV_WILLNEED
    , sysPosix_MADV_DONTNEED :: CMemAdvice
#if defined(POSIX_MADV_NORMAL)
sysPosix_MADV_NORMAL     = (#const POSIX_MADV_NORMAL)
sysPosix_MADV_RANDOM     = (#const POSIX_MADV_RANDOM)
sysPosix_MADV_SEQUENTIAL = (#const POSIX_MADV_SEQUENTIAL)
sysPosix_MADV_WILLNEED   = (#const POSIX_MADV_WILLNEED)
sysPosix_MADV_DONTNEED   = (#const POSIX_MADV_DONTNEED)
#else
sysPosix_MADV_NORMAL     = (#const MADV_NORMAL)
sysPosix_MADV_RANDOM     = (#const MADV_RANDOM)
sysPosix_MADV_SEQUENTIAL = (#const MADV_SEQUENTIAL)
sysPosix_MADV_WILLNEED   = (#const MADV_WILLNEED)
sysPosix_MADV_DONTNEED   = (#const MADV_DONTNEED)
#endif

sysPosix_MS_ASYNC
    , sysPosix_MS_SYNC
    , sysPosix_MS_INVALIDATE :: CMemSyncFlags
sysPosix_MS_ASYNC      = (#const MS_ASYNC)
sysPosix_MS_SYNC       = (#const MS_SYNC)
sysPosix_MS_INVALIDATE = (#const MS_INVALIDATE)

foreign import ccall unsafe "mmap"
    sysPosixMmap :: Ptr a -> CSize -> CMemProtFlags -> CMemMappingFlags -> CFd -> COff -> IO (Ptr a)

foreign import ccall unsafe "munmap"
    sysPosixMunmap :: Ptr a -> CSize -> IO CInt

#if defined(POSIX_MADV_NORMAL)
foreign import ccall unsafe "posix_madvise"
    sysPosixMadvise :: Ptr a -> CSize -> CMemAdvice -> IO CInt
#else
foreign import ccall unsafe "madvise"
    sysPosixMadvise :: Ptr a -> CSize -> CMemAdvice -> IO CInt
#endif

foreign import ccall unsafe "msync"
    sysPosixMsync :: Ptr a -> CSize -> CMemSyncFlags -> IO CInt

foreign import ccall unsafe "mprotect"
    sysPosixMprotect :: Ptr a -> CSize -> CMemProtFlags -> IO CInt

#ifndef __HAIKU__
foreign import ccall unsafe "mlock"
    sysPosixMlock :: Ptr a -> CSize -> IO CInt
#else
sysPosixMlock :: Ptr a -> CSize -> IO CInt
sysPosixMlock _ _ = return (-1)
#endif

#ifndef __HAIKU__
foreign import ccall unsafe "munlock"
    sysPosixMunlock :: Ptr a -> CSize -> IO CInt
#else
sysPosixMunlock :: Ptr a -> CSize -> IO CInt
sysPosixMunlock _ _ = return (-1)
#endif

sysPosix_SC_PAGESIZE :: CSysconfName
sysPosix_SC_PAGESIZE = (#const _SC_PAGESIZE)

foreign import ccall unsafe "sysconf"
    sysPosixSysconf :: CSysconfName -> CLong
--------------------------------------------------------------------------------
-- files
--------------------------------------------------------------------------------
foreign import ccall unsafe "open"
    sysPosixOpen :: Ptr CChar -> COpenFlags -> CMode -> IO CFd
foreign import ccall unsafe "openat"
    sysPosixOpenAt :: CFd -> Ptr CChar -> COpenFlags -> CMode -> IO CFd
foreign import ccall unsafe "close"
    sysPosixClose :: CFd -> IO CInt

foreign import capi "fcntl.h fcntl"
    sysPosixFnctlNoArg :: CFd -> CInt -> IO CInt
foreign import capi "fcntl.h fcntl"
    sysPosixFnctlPtr :: CFd -> CInt -> Ptr a -> IO CInt

foreign import ccall unsafe "ftruncate"
    sysPosixFtruncate :: CFd -> COff -> IO CInt

--------------------------------------------------------------------------------
-- directories
--------------------------------------------------------------------------------

foreign import ccall unsafe "opendir"
    sysPosixOpendir :: Ptr CChar -> IO (Ptr CDir)
foreign import ccall unsafe "fdopendir"
    sysPosixFdopendir :: CFd -> IO (Ptr CDir)
foreign import ccall unsafe "readdir"
    sysPosixReaddir :: Ptr CDir -> IO (Ptr CDirent)
foreign import ccall unsafe "readdir_r"
    sysPosixReaddirR :: Ptr CDir -> Ptr CDirent -> Ptr (Ptr CDirent) -> IO CInt
foreign import ccall unsafe "telldir"
    sysPosixTelldir :: Ptr CDir -> IO CLong
foreign import ccall unsafe "seekdir"
    sysPosixSeekdir :: Ptr CDir -> CLong -> IO ()
foreign import ccall unsafe "rewinddir"
    sysPosixRewinddir :: Ptr CDir -> IO ()
foreign import ccall unsafe "closedir"
    sysPosixClosedir :: Ptr CDir -> IO CInt
foreign import ccall unsafe "dirfd"
    sysPosixDirfd :: Ptr CDir -> IO CFd
