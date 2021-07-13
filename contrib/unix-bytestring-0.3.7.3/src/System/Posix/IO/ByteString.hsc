{-
/N.B./, There's a bug when trying to use Cabal-style MIN_VERSION_foo(1,2,3)
macros in combination with hsc2hs. We don't need full hsc2hs support
in this file, but if we use CPP instead we get a strange error on
OSX 10.5.8 about "architecture not supported" (even though the
headers work fine with hsc2hs). It turns out that we don't /need/
to combine Cabal-style macros and hsc2hs\/cpp since we can remove
our dependency on the @unix@ package. But this issue is worth making
a note of.
-}

-- GHC 7.6 changed the semantics of the FFI so that we must have
-- the data constructors in scope in order to import functions using
-- the given types. However, those data constructors[1] are not exported
-- in earlier versions, so having @(..)@ will raise warnings on old
-- systems. However, Cabal-style MIN_VERSION_foo(1,2,3) macros don't
-- play nicely with hsc2hs; and we need hsc2hs in lieu of CPP for
-- OS X. So we disable -Wall rather than trying to CPP this problem
-- away. There doesn't appear to be a -fno-warn-foo for this
-- particular issue.
--
-- [1] CSsize(..), COff(..), CInt(..), CSize(..), CChar(..)

{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2013.08.08
-- |
-- Module      :  System.Posix.IO.ByteString
-- Copyright   :  Copyright (c) 2010--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (POSIX.1, XPG4.2; hsc2hs, FFI)
--
-- Provides a strict-'BS.ByteString' file-descriptor based I\/O
-- API, designed loosely after the @String@ file-descriptor based
-- I\/O API in "System.Posix.IO". The functions here wrap standard
-- C implementations of the functions specified by the ISO\/IEC
-- 9945-1:1990 (``POSIX.1'') and X\/Open Portability Guide Issue
-- 4, Version 2 (``XPG4.2'') specifications.
----------------------------------------------------------------
module System.Posix.IO.ByteString
    (
    -- * I\/O with file descriptors
    -- ** Reading
    -- *** The POSIX.1 @read(2)@ syscall
      fdRead
    , fdReadBuf
    , tryFdReadBuf
    , fdReads
    -- *** The XPG4.2 @readv(2)@ syscall
    -- , fdReadv
    , fdReadvBuf
    , tryFdReadvBuf
    -- *** The XPG4.2 @pread(2)@ syscall
    , fdPread
    , fdPreadBuf
    , tryFdPreadBuf
    , fdPreads
    
    -- ** Writing
    -- *** The POSIX.1 @write(2)@ syscall
    , fdWrite
    , fdWriteBuf
    , tryFdWriteBuf
    , fdWrites
    -- *** The XPG4.2 @writev(2)@ syscall
    , fdWritev
    , fdWritevBuf
    , tryFdWritevBuf
    -- *** The XPG4.2 @pwrite(2)@ syscall
    , fdPwrite
    , fdPwriteBuf
    , tryFdPwriteBuf
    
    -- ** Seeking
    -- | These functions are not 'ByteString' related, but are
    -- provided here for API completeness.

    -- *** The POSIX.1 @lseek(2)@ syscall
    , fdSeek
    , tryFdSeek
    ) where

import           Data.Word                (Word8)
import qualified Data.ByteString          as BS
import qualified Data.ByteString.Internal as BSI
import qualified Data.ByteString.Unsafe   as BSU

import           System.IO                (SeekMode(..))
import qualified System.IO.Error          as IOE
import qualified System.Posix.Internals   as Base
import           System.Posix.Types.Iovec
import           System.Posix.Types       ( Fd, ByteCount, FileOffset
                                          , CSsize(..), COff(..))
import           Foreign.C.Types          (CInt(..), CSize(..), CChar(..))

import qualified Foreign.C.Error          as C
import           Foreign.C.Error.Safe
import           Foreign.Ptr              (Ptr, castPtr, plusPtr)
import qualified Foreign.Marshal.Array    as FMA (withArrayLen)

-- For the functor instance of 'Either', aka 'right' for ArrowChoice(->)
import Control.Arrow (ArrowChoice(..))

-- iovec, writev, and readv are in <sys/uio.h>, but we must include
-- <sys/types.h> and <unistd.h> for legacy reasons.
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

----------------------------------------------------------------
-- | Throw an 'IOE.IOError' for EOF.
ioErrorEOF :: String -> IO a
ioErrorEOF fun =
    IOE.ioError
        (IOE.ioeSetErrorString
            (IOE.mkIOError IOE.eofErrorType fun Nothing Nothing)
            "EOF")


----------------------------------------------------------------
foreign import ccall safe "read"
    -- ssize_t read(int fildes, void *buf, size_t nbyte);
    c_safe_read :: CInt -> Ptr CChar -> CSize -> IO CSsize


-- | Read data from an 'Fd' into memory. This is exactly equivalent
-- to the POSIX.1 @read(2)@ system call, except that we return 0
-- bytes read if the @ByteCount@ argument is less than or equal to
-- zero (instead of throwing an errno exception). /N.B./, this
-- behavior is different from the version in @unix-2.4.2.0@ which
-- only checks for equality to zero. If there are any errors, then
-- they are thrown as 'IOE.IOError' exceptions.
--
-- /Since: 0.3.0/
fdReadBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory in which to put the data.
    -> ByteCount    -- ^ How many bytes to try to read.
    -> IO ByteCount -- ^ How many bytes were actually read (zero for EOF).
fdReadBuf fd buf nbytes
    | nbytes <= 0 = return 0
    | otherwise   =
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdReadBuf
                $ c_safe_read
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)

_fdReadBuf :: String
_fdReadBuf = "System.Posix.IO.ByteString.fdReadBuf"
{-# NOINLINE _fdReadBuf #-}


-- | Read data from an 'Fd' into memory. This is a variation of
-- 'fdReadBuf' which returns errors with an 'Either' instead of
-- throwing exceptions.
--
-- /Since: 0.3.3/
tryFdReadBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory in which to put the data.
    -> ByteCount    -- ^ How many bytes to try to read.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually read (zero for EOF).
tryFdReadBuf fd buf nbytes
    | nbytes <= 0 = return (Right 0)
    | otherwise   =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_read
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)


----------------------------------------------------------------
-- | Read data from an 'Fd' and convert it to a 'BS.ByteString'.
-- Throws an exception if this is an invalid descriptor, or EOF has
-- been reached. This is essentially equivalent to 'fdReadBuf'; the
-- differences are that we allocate a byte buffer for the @ByteString@,
-- and that we detect EOF and throw an 'IOE.IOError'.
fdRead
    :: Fd
    -> ByteCount        -- ^ How many bytes to try to read.
    -> IO BS.ByteString -- ^ The bytes read.
fdRead fd nbytes
    | nbytes <= 0 = return BS.empty
    | otherwise   = 
        BSI.createAndTrim (fromIntegral nbytes) $ \buf -> do
            rc <- fdReadBuf fd buf nbytes
            if 0 == rc
                then ioErrorEOF _fdRead
                else return (fromIntegral rc)

_fdRead :: String
_fdRead = "System.Posix.IO.ByteString.fdRead"
{-# NOINLINE _fdRead #-}


----------------------------------------------------------------
-- | Read data from an 'Fd' and convert it to a 'BS.ByteString'.
-- Throws an exception if this is an invalid descriptor, or EOF has
-- been reached.
--
-- This version takes a kind of stateful predicate for whether and
-- how long to keep retrying. Assume the function is called as
-- @fdReads f z0 fd n0@. We will attempt to read @n0@ bytes from
-- @fd@. If we fall short, then we will call @f len z@ where @len@
-- is the total number of bytes read so far and @z@ is the current
-- state (initially @z0@). If it returns @Nothing@ then we will
-- give up and return the current buffer; otherwise we will retry
-- with the new state, continuing from where we left off.
--
-- For example, to define a function that tries up to @n@ times,
-- we can use:
--
-- > fdReadUptoNTimes :: Int -> Fd -> ByteCount -> IO ByteString
-- > fdReadUptoNTimes n0 = fdReads retry n0
-- >     where
-- >     retry _ 0 = Nothing
-- >     retry _ n = Just $! n-1
--
-- The benefit of doing this instead of the naive approach of calling
-- 'fdRead' repeatedly is that we only need to allocate one byte
-- buffer, and trim it once at the end--- whereas the naive approach
-- would allocate a buffer, trim it to the number of bytes read,
-- and then concatenate with the previous one (another allocation,
-- plus copying everything over) for each time around the loop.
--
-- /Since: 0.2.1/
fdReads
    :: (ByteCount -> a -> Maybe a) -- ^ A stateful predicate for retrying.
    -> a                           -- ^ An initial state for the predicate.
    -> Fd
    -> ByteCount                   -- ^ How many bytes to try to read.
    -> IO BS.ByteString            -- ^ The bytes read.
fdReads f z0 fd n0
    | n0 <= 0   = return BS.empty
    | otherwise = BSI.createAndTrim (fromIntegral n0) (go z0 0 n0)
    where
    go _ len n buf | len `seq` n `seq` buf `seq` False = undefined
    go z len n buf = do
        rc <- fdReadBuf fd buf n
        let len' = len + rc
        case rc of
          _ | rc == 0 -> ioErrorEOF _fdReads
            | rc == n -> return (fromIntegral len') -- Finished.
            | otherwise ->
                case f len' z of
                Nothing -> return (fromIntegral len') -- Gave up.
                Just z' ->
                    go z' len' (n - rc) (buf `plusPtr` fromIntegral rc)

_fdReads :: String
_fdReads = "System.Posix.IO.ByteString.fdReads"
{-# NOINLINE _fdReads #-}


----------------------------------------------------------------
foreign import ccall safe "readv"
    -- ssize_t readv(int fildes, const struct iovec *iov, int iovcnt);
    c_safe_readv :: CInt -> Ptr CIovec -> CInt -> IO CSsize
{-
-- N.B., c_safe_readv will throw errno=EINVAL
-- if iovcnt <= 0 || > 16,
-- if one of the iov_len values in the iov array was negative,
-- if the sum of the iov_len values in the iov array overflowed a 32-bit integer.
    
fdReadvBufSafe :: Fd -> Ptr CIovec -> Int -> IO ByteCount
fdReadvBufSafe fd = go 0
    where
    go rc bufs len
        | len <= 0  = return rc
        | otherwise = do
            m <- checkIovecs bufs (min 16 len)
            case m of
                Nothing                 -> error
                Just (bufs', l, nbytes) -> do
                    rc' <- fdReadvBuf fd bufs l
                    if rc' == nbytes
                        then go (rc+rc') bufs' (len-l)
                        else return (rc+rc')

checkIovecs :: Ptr CIovec -> Int -> IO (Maybe (Ptr CIovec, Int, ByteCount))
checkIovecs = go (0 :: Int32) 0
    where
    go nbytes n p len
        | nbytes `seq` n `seq` p `seq` len `seq` False = undefined
        | len == 0  = return (Just (p, n, fromIntegral nbytes)
        | otherwise = do
            l <- iov_len <$> peek p
            if l < 0
                then return Nothing
                else do
                    let nbytes' = nbytes+l
                    if nbytes' < 0
                        then return (Just (p, n, fromIntegral nbytes)
                        else go nbytes' (n+1) (p++) (len-1)
-}


-- | Read data from an 'Fd' and scatter it into memory. This is
-- exactly equivalent to the XPG4.2 @readv(2)@ system call, except
-- that we return 0 bytes read if the @Int@ argument is less than
-- or equal to zero (instead of throwing an 'C.eINVAL' exception).
-- If there are any errors, then they are thrown as 'IOE.IOError'
-- exceptions.
--
-- TODO: better documentation.
--
-- /Since: 0.3.0/
fdReadvBuf
    :: Fd
    -> Ptr CIovec   -- ^ A C-style array of buffers to fill.
    -> Int          -- ^ How many buffers there are.
    -> IO ByteCount -- ^ How many bytes were actually read (zero for EOF).
fdReadvBuf fd bufs len
    | len <= 0  = return 0
    | otherwise =
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdReadvBuf
                $ c_safe_readv (fromIntegral fd) bufs (fromIntegral len)

_fdReadvBuf :: String
_fdReadvBuf = "System.Posix.IO.ByteString.fdReadvBuf"
{-# NOINLINE _fdReadvBuf #-}


-- | Read data from an 'Fd' and scatter it into memory. This is a
-- variation of 'fdReadvBuf' which returns errors with an 'Either'
-- instead of throwing exceptions.
--
-- /Since: 0.3.3/
tryFdReadvBuf
    :: Fd
    -> Ptr CIovec   -- ^ A C-style array of buffers to fill.
    -> Int          -- ^ How many buffers there are.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually read (zero for EOF).
tryFdReadvBuf fd bufs len
    | len <= 0  = return (Right 0)
    | otherwise =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_readv (fromIntegral fd) bufs (fromIntegral len)


-- TODO: What's a reasonable wrapper for fdReadvBuf to make it Haskellish?

----------------------------------------------------------------
foreign import ccall safe "pread"
    -- ssize_t pread(int fildes, void *buf, size_t nbyte, off_t offset);
    c_safe_pread :: CInt -> Ptr Word8 -> CSize -> COff -> IO CSsize


-- | Read data from a specified position in the 'Fd' into memory,
-- without altering the position stored in the @Fd@. This is exactly
-- equivalent to the XPG4.2 @pread(2)@ system call, except that we
-- return 0 bytes read if the @Int@ argument is less than or equal
-- to zero (instead of throwing an errno exception). If there are
-- any errors, then they are thrown as 'IOE.IOError' exceptions.
--
-- /Since: 0.3.0/
fdPreadBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory in which to put the data.
    -> ByteCount    -- ^ How many bytes to try to read.
    -> FileOffset   -- ^ Where to read the data from.
    -> IO ByteCount -- ^ How many bytes were actually read (zero for EOF).
fdPreadBuf fd buf nbytes offset
    | nbytes <= 0 = return 0
    | otherwise   =
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdPreadBuf
                $ c_safe_pread
                    (fromIntegral fd)
                    buf
                    (fromIntegral nbytes)
                    (fromIntegral offset)

_fdPreadBuf :: String
_fdPreadBuf = "System.Posix.IO.ByteString.fdPreadBuf"
{-# NOINLINE _fdPreadBuf #-}


-- | Read data from a specified position in the 'Fd' into memory,
-- without altering the position stored in the @Fd@. This is a
-- variation of 'fdPreadBuf' which returns errors with an 'Either'
-- instead of throwing exceptions.
--
-- /Since: 0.3.3/
tryFdPreadBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory in which to put the data.
    -> ByteCount    -- ^ How many bytes to try to read.
    -> FileOffset   -- ^ Where to read the data from.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually read (zero for EOF).
tryFdPreadBuf fd buf nbytes offset
    | nbytes <= 0 = return (Right 0)
    | otherwise   =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_pread
                    (fromIntegral fd)
                    buf
                    (fromIntegral nbytes)
                    (fromIntegral offset)

----------------------------------------------------------------
-- | Read data from a specified position in the 'Fd' and convert
-- it to a 'BS.ByteString', without altering the position stored
-- in the @Fd@. Throws an exception if this is an invalid descriptor,
-- or EOF has been reached. This is essentially equivalent to
-- 'fdPreadBuf'; the differences are that we allocate a byte buffer
-- for the @ByteString@, and that we detect EOF and throw an
-- 'IOE.IOError'.
--
-- /Since: 0.3.0/
fdPread
    :: Fd
    -> ByteCount        -- ^ How many bytes to try to read.
    -> FileOffset       -- ^ Where to read the data from.
    -> IO BS.ByteString -- ^ The bytes read.
fdPread fd nbytes offset
    | nbytes <= 0 = return BS.empty
    | otherwise   =
        BSI.createAndTrim (fromIntegral nbytes) $ \buf -> do
            rc <- fdPreadBuf fd buf nbytes offset
            if 0 == rc
                then ioErrorEOF _fdPread
                else return (fromIntegral rc)

_fdPread :: String
_fdPread = "System.Posix.IO.ByteString.fdPread"
{-# NOINLINE _fdPread #-}

----------------------------------------------------------------
-- | Read data from a specified position in the 'Fd' and convert
-- it to a 'BS.ByteString', without altering the position stored
-- in the @Fd@. Throws an exception if this is an invalid descriptor,
-- or EOF has been reached. This is a 'fdPreadBuf' based version
-- of 'fdReads'; see those functions for more details.
--
-- /Since: 0.3.1/
fdPreads
    :: (ByteCount -> a -> Maybe a) -- ^ A stateful predicate for retrying.
    -> a                           -- ^ An initial state for the predicate.
    -> Fd
    -> ByteCount                   -- ^ How many bytes to try to read.
    -> FileOffset                  -- ^ Where to read the data from.
    -> IO BS.ByteString            -- ^ The bytes read.
fdPreads f z0 fd n0 offset
    | n0 <= 0   = return BS.empty
    | otherwise = BSI.createAndTrim (fromIntegral n0) (go z0 0 n0)
    where
    go _ len n buf | len `seq` n `seq` buf `seq` False = undefined
    go z len n buf = do
        rc <- fdPreadBuf fd buf n (offset + fromIntegral len)
        let len' = len + rc
        case rc of
          _ | rc == 0 -> ioErrorEOF _fdPreads
            | rc == n -> return (fromIntegral len') -- Finished.
            | otherwise ->
                case f len' z of
                Nothing -> return (fromIntegral len') -- Gave up.
                Just z' ->
                    go z' len' (n - rc) (buf `plusPtr` fromIntegral rc)

_fdPreads :: String
_fdPreads = "System.Posix.IO.ByteString.fdPreads"
{-# NOINLINE _fdPreads #-}

----------------------------------------------------------------
----------------------------------------------------------------
foreign import ccall safe "write" 
    -- ssize_t write(int fildes, const void *buf, size_t nbyte);
    c_safe_write :: CInt -> Ptr CChar -> CSize -> IO CSsize


-- | Write data from memory to an 'Fd'. This is exactly equivalent
-- to the POSIX.1 @write(2)@ system call, except that we return 0
-- bytes written if the @ByteCount@ argument is less than or equal
-- to zero (instead of throwing an errno exception). /N.B./, this
-- behavior is different from the version in @unix-2.4.2.0@ which
-- doesn't check the byte count. If there are any errors, then they
-- are thrown as 'IOE.IOError' exceptions.
--
-- /Since: 0.3.0/
fdWriteBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory containing the data to write.
    -> ByteCount    -- ^ How many bytes to try to write.
    -> IO ByteCount -- ^ How many bytes were actually written.
fdWriteBuf fd buf nbytes
    | nbytes <= 0 = return 0
    | otherwise   = 
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdWriteBuf
                $ c_safe_write
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)

_fdWriteBuf :: String
_fdWriteBuf = "System.Posix.IO.ByteString.fdWriteBuf"
{-# NOINLINE _fdWriteBuf #-}


-- | Write data from memory to an 'Fd'. This is a variation of
-- 'fdWriteBuf' which returns errors with an 'Either' instead of
-- throwing exceptions.
--
-- /Since: 0.3.3/
tryFdWriteBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory containing the data to write.
    -> ByteCount    -- ^ How many bytes to try to write.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually read (zero for EOF).
tryFdWriteBuf fd buf nbytes
    | nbytes <= 0 = return (Right 0)
    | otherwise   =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_write
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)

----------------------------------------------------------------
-- | Write a 'BS.ByteString' to an 'Fd'. The return value is the
-- total number of bytes actually written. This is exactly equivalent
-- to 'fdWriteBuf'; we just convert the @ByteString@ into its
-- underlying @Ptr Word8@ and @ByteCount@ components for passing
-- to 'fdWriteBuf'.
fdWrite
    :: Fd
    -> BS.ByteString -- ^ The string to write.
    -> IO ByteCount  -- ^ How many bytes were actually written.
fdWrite fd s =
    -- N.B., BSU.unsafeUseAsCStringLen does zero copying. Use
    -- BS.useAsCStringLen if there's any chance fdWriteBuf might
    -- alter the buffer.
    BSU.unsafeUseAsCStringLen s $ \(buf,len) -> do
        fdWriteBuf fd (castPtr buf) (fromIntegral len)


----------------------------------------------------------------
-- | Write a sequence of 'BS.ByteString's to an 'Fd'. The return
-- value is a triple of: the total number of bytes written, the
-- number of bytes written from the first of the remaining strings,
-- and the remaining (unwritten) strings. We return this triple
-- instead of a pair adjusting the head of the remaining strings
-- (i.e., removing the bytes already written) in case there is some
-- semantic significance to the way the input is split into chunks.
--
-- This version consumes the list lazily and will call 'fdWrite'
-- once for each @ByteString@, thus making /O(n)/ system calls.
-- This laziness allows the early parts of the list to be garbage
-- collected and prevents needing to hold the whole list of
-- @ByteString@s in memory at once. Compare against 'fdWritev'.
fdWrites
    :: Fd
    -> [BS.ByteString]
        -- ^ The strings to write.
    -> IO (ByteCount, ByteCount, [BS.ByteString])
        -- ^ The total number of bytes written, the number of bytes
        -- written from the first of the remaining strings, the
        -- remaining (unwritten) strings.
fdWrites fd = go 0
    where
    -- We want to do a left fold in order to avoid stack overflows,
    -- but we need to have an early exit for incomplete writes
    -- (which normally requires a right fold). Hence this recursion.
    go acc []         = return (acc, 0, [])
    go acc ccs@(c:cs) = do
        rc <- fdWrite fd c
        let acc' = acc+rc in acc' `seq` do
        if rc == fromIntegral (BS.length c)
            then go acc' cs
            else return (acc', rc, ccs)


----------------------------------------------------------------
foreign import ccall safe "writev"
    -- ssize_t writev(int fildes, const struct iovec *iov, int iovcnt);
    c_safe_writev :: CInt -> Ptr CIovec -> CInt -> IO CSsize
{-
-- N.B., c_safe_readv will throw errno=EINVAL
-- if iovcnt is less than or equal to 0, or greater than UIO_MAXIOV. (BUG: I have no idea where UIO_MAXIOV is defined! The web says it's in <linux/uio.h>, and some suggest using <limits.h>IOV_MAX or <limits.h>_XOPEN_IOV_MAX instead.)
-- <http://www.mail-archive.com/freebsd-current@freebsd.org/msg27878.html>
-- <http://www.mail-archive.com/naviserver-devel@lists.sourceforge.net/msg02237.html>
-- -- That last link says that glibc might transparently chop up larger values before sending to the kernel.
-- if one of the iov_len values in the iov array is negative.
-- if the sum of the iov_len values in the iov array overflows a 32-bit integer.
-}


-- | Write data from memory to an 'Fd'. This is exactly equivalent
-- to the XPG4.2 @writev(2)@ system call, except that we return 0
-- bytes written if the @Int@ argument is less than or equal to
-- zero (instead of throwing an 'C.eINVAL' exception). If there are
-- any errors, then they are thrown as 'IOE.IOError' exceptions.
--
-- TODO: better documentation.
--
-- /Since: 0.3.0/
fdWritevBuf
    :: Fd
    -> Ptr CIovec   -- ^ A C-style array of buffers to write.
    -> Int          -- ^ How many buffers there are.
    -> IO ByteCount -- ^ How many bytes were actually written.
fdWritevBuf fd bufs len
    | len <= 0  = return 0
    | otherwise =
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdWritevBuf
                $ c_safe_writev (fromIntegral fd) bufs (fromIntegral len)

_fdWritevBuf :: String
_fdWritevBuf = "System.Posix.IO.ByteString.fdWritevBuf"
{-# NOINLINE _fdWritevBuf #-}


-- | Write data from memory to an 'Fd'. This is a variation of
-- 'fdWritevBuf' which returns errors with an 'Either' instead of
-- throwing exceptions.
--
-- /Since: 0.3.3/
tryFdWritevBuf
    :: Fd
    -> Ptr CIovec   -- ^ A C-style array of buffers to write.
    -> Int          -- ^ How many buffers there are.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually read (zero for EOF).
tryFdWritevBuf fd bufs len
    | len <= 0  = return (Right 0)
    | otherwise =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_writev (fromIntegral fd) bufs (fromIntegral len)


----------------------------------------------------------------
-- | Write a sequence of 'BS.ByteString's to an 'Fd'. The return
-- value is the total number of bytes written. Unfortunately the
-- @writev(2)@ system call does not provide enough information to
-- return the triple that 'fdWrites' does.
--
-- This version will force the spine of the list, converting each
-- @ByteString@ into an @iovec@ (see 'CIovec'), and then call
-- 'fdWritevBuf'. This means we only make one system call, which
-- reduces the overhead of performing context switches. But it also
-- means that we must store the whole list of @ByteString@s in
-- memory at once, and that we must perform some allocation and
-- conversion. Compare against 'fdWrites'.
fdWritev
    :: Fd
    -> [BS.ByteString] -- ^ The strings to write.
    -> IO ByteCount    -- ^ How many bytes were actually written.
fdWritev fd cs = do
    rc <- FMA.withArrayLen (map unsafeByteString2CIovec cs) $ \len iovs ->
        fdWritevBuf fd iovs (fromIntegral len)
    -- BUG: is this enough to actually hold onto them?
    mapM_ touchByteString cs
    return rc


----------------------------------------------------------------
foreign import ccall safe "pwrite"
    -- ssize_t pwrite(int fildes, const void *buf, size_t nbyte, off_t offset);
    c_safe_pwrite :: CInt -> Ptr Word8 -> CSize -> COff -> IO CSsize


-- | Write data from memory to a specified position in the 'Fd',
-- but without altering the position stored in the @Fd@. This is
-- exactly equivalent to the XPG4.2 @pwrite(2)@ system call, except
-- that we return 0 bytes written if the @ByteCount@ argument is
-- less than or equal to zero (instead of throwing an errno exception).
-- If there are any errors, then they are thrown as 'IOE.IOError'
-- exceptions.
--
-- /Since: 0.3.0/
fdPwriteBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory containing the data to write.
    -> ByteCount    -- ^ How many bytes to try to write.
    -> FileOffset   -- ^ Where to write the data to.
    -> IO ByteCount -- ^ How many bytes were actually written.
fdPwriteBuf fd buf nbytes offset
    | nbytes <= 0 = return 0
    | otherwise   =
        fmap fromIntegral
            $ C.throwErrnoIfMinus1Retry _fdPwriteBuf
                $ c_safe_pwrite
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)
                    (fromIntegral offset)

_fdPwriteBuf :: String
_fdPwriteBuf = "System.Posix.IO.ByteString.fdPwriteBuf"
{-# NOINLINE _fdPwriteBuf #-}


-- | Write data from memory to a specified position in the 'Fd',
-- but without altering the position stored in the @Fd@. This is a
-- variation of 'fdPwriteBuf' which returns errors with an 'Either'
-- instead of throwing exceptions.
--
-- /Since: 0.3.3/
tryFdPwriteBuf
    :: Fd
    -> Ptr Word8    -- ^ Memory containing the data to write.
    -> ByteCount    -- ^ How many bytes to try to write.
    -> FileOffset   -- ^ Where to write the data to.
    -> IO (Either C.Errno ByteCount)
        -- ^ How many bytes were actually written.
tryFdPwriteBuf fd buf nbytes offset
    | nbytes <= 0 = return (Right 0)
    | otherwise   =
        fmap (right fromIntegral)
            $ eitherErrnoIfMinus1Retry
                $ c_safe_pwrite
                    (fromIntegral fd)
                    (castPtr buf)
                    (fromIntegral nbytes)
                    (fromIntegral offset)


----------------------------------------------------------------
-- | Write data from memory to a specified position in the 'Fd',
-- but without altering the position stored in the @Fd@. This is
-- exactly equivalent to 'fdPwriteBuf'; we just convert the
-- @ByteString@ into its underlying @Ptr Word8@ and @ByteCount@
-- components for passing to 'fdPwriteBuf'.
--
-- /Since: 0.3.0/
fdPwrite
    :: Fd
    -> BS.ByteString -- ^ The string to write.
    -> FileOffset    -- ^ Where to write the data to.
    -> IO ByteCount  -- ^ How many bytes were actually written.
fdPwrite fd s offset =
    -- N.B., BSU.unsafeUseAsCStringLen does zero copying. Use
    -- BS.useAsCStringLen if there's any chance fdPwriteBuf might
    -- alter the buffer.
    BSU.unsafeUseAsCStringLen s $ \(buf,len) -> do
        fdPwriteBuf fd (castPtr buf) (fromIntegral len) offset


----------------------------------------------------------------

mode2Int :: SeekMode -> CInt
mode2Int AbsoluteSeek = (#const SEEK_SET)
mode2Int RelativeSeek = (#const SEEK_CUR)
mode2Int SeekFromEnd  = (#const SEEK_END)


-- | Repositions the offset of the file descriptor according to the
-- offset and the seeking mode. This is exactly equivalent to the
-- POSIX.1 @lseek(2)@ system call. If there are any errors, then
-- they are thrown as 'IOE.IOError' exceptions.
--
-- This is the same as 'System.Posix.IO.fdSeek' in @unix-2.6.0.1@,
-- but provided here for consistency.
--
-- /Since: 0.3.5/
fdSeek :: Fd -> SeekMode -> FileOffset -> IO FileOffset
fdSeek fd mode off =
    C.throwErrnoIfMinus1 "fdSeek"
        $ Base.c_lseek (fromIntegral fd) off (mode2Int mode)


-- | Repositions the offset of the file descriptor according to the
-- offset and the seeking mode. This is a variation of 'fdSeek'
-- which returns errors with an @Either@ instead of throwing
-- exceptions.
--
-- /Since: 0.3.5/
tryFdSeek :: Fd -> SeekMode -> FileOffset -> IO (Either C.Errno FileOffset)
tryFdSeek fd mode off =
    eitherErrnoIfMinus1
        $ Base.c_lseek (fromIntegral fd) off (mode2Int mode)

----------------------------------------------------------------
----------------------------------------------------------- fin.
