{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- TODO: cf <http://hpaste.org/76873>
----------------------------------------------------------------
--                                                    2011.03.17
-- |
-- Module      :  System.Posix.IO.ByteString.Lazy
-- Copyright   :  Copyright (c) 2010--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (requires POSIX.1, XPG4.2)
--
-- Provides a lazy-'BL.ByteString' file-descriptor based I\/O
-- API, designed loosely after the @String@ file-descriptor based
-- I\/O API in "System.Posix.IO". The functions here wrap standard
-- C implementations of the functions specified by the ISO\/IEC
-- 9945-1:1990 (``POSIX.1'') and X\/Open Portability Guide Issue
-- 4, Version 2 (``XPG4.2'') specifications.
--
-- These functions are provided mainly as a convenience to avoid
-- boilerplate code converting between lazy 'BL.ByteString' and
-- strict @['BS.ByteString']@. It may be depricated in the future.
----------------------------------------------------------------
module System.Posix.IO.ByteString.Lazy
    (
    -- * I\/O with file descriptors
    -- ** Reading
      fdRead
    , fdPread
    -- ** Writing
    , fdWrites
    , fdWritev
    ) where

import qualified Data.ByteString               as BS
import qualified Data.ByteString.Unsafe        as BSU
import qualified System.Posix.IO.ByteString    as PosixBS
import qualified Data.ByteString.Lazy          as BL
import qualified Data.ByteString.Lazy.Internal as BLI
import           System.Posix.Types            (Fd, ByteCount, FileOffset)

----------------------------------------------------------------
-- | Read data from an 'Fd' and convert it to a 'BL.ByteString'.
-- Throws an exception if this is an invalid descriptor, or EOF has
-- been reached. This is a thin wrapper around 'PosixBS.fdRead'.
fdRead
    :: Fd
    -> ByteCount        -- ^ How many bytes to try to read.
    -> IO BL.ByteString -- ^ The bytes read.
fdRead fd nbytes
    | nbytes <= 0 = return BL.empty
    | otherwise   = do
        s <- PosixBS.fdRead fd nbytes
        return (BLI.chunk s BL.empty)

----------------------------------------------------------------
-- | Read data from a specified position in the 'Fd' and convert
-- it to a 'BS.ByteString', without altering the position stored
-- in the @Fd@. Throws an exception if this is an invalid descriptor,
-- or EOF has been reached. This is a thin wrapper around
-- 'PosixBS.fdPread'.
--
-- /Since: 0.3.1/
fdPread
    :: Fd
    -> ByteCount        -- ^ How many bytes to try to read.
    -> FileOffset       -- ^ Where to read the data from.
    -> IO BL.ByteString -- ^ The bytes read.
fdPread fd nbytes offset
    | nbytes <= 0 = return BL.empty
    | otherwise   = do
        s <- PosixBS.fdPread fd nbytes offset
        return (BLI.chunk s BL.empty)


----------------------------------------------------------------
-- | Write a 'BL.ByteString' to an 'Fd'. This function makes one
-- @write(2)@ system call per chunk, as per 'PosixBS.fdWrites'.
fdWrites
    :: Fd
    -> BL.ByteString
        -- ^ The string to write.
    -> IO (ByteCount, BL.ByteString)
        -- ^ How many bytes were actually written, and the remaining
        -- (unwritten) string.
fdWrites fd = go 0
    where
    -- We want to do a left fold in order to avoid stack overflows,
    -- but we need to have an early exit for incomplete writes
    -- (which normally requires a right fold). Hence this recursion.
    go acc BLI.Empty        = return (acc, BL.empty)
    go acc (BLI.Chunk c cs) = do
        rc <- PosixBS.fdWrite fd c
        let acc'  = acc+rc          in acc'  `seq` do
        let rcInt = fromIntegral rc in rcInt `seq` do
        if rcInt == BS.length c
            then go acc' cs
            else return (acc', BLI.Chunk (BSU.unsafeDrop rcInt c) cs)
{-
Using 'BSU.unsafeDrop' above is safe, assuming that
'System.Posix.IO.fdWriteBuf' never returns (rc < 0 || rc > BS.length c).
If we are paranoid about that then we should do the following instead:

    go acc ccs =
        case ccs of
        BLI.Empty      -> return (acc, ccs)
        BLI.Chunk c cs -> do
            rc <- PosixBS.fdWrite fd c
            let acc'  = acc+rc          in acc'  `seq` do
            let rcInt = fromIntegral rc in rcInt `seq` do
            case BS.length c of
                len | rcInt == len -> go acc' cs
                    | rcInt >  len -> error _impossibleByteCount
                    | rcInt <  0   -> error _negtiveByteCount
                    | rcInt == 0   -> return (acc', ccs) -- trivial optimizing
                    | otherwise    -> return (acc', BLI.Chunk (BSU.unsafeDrop rcInt c) cs)

_negtiveByteCount =
    "System.Posix.IO.fdWriteBuf: returned a negative byte count"
_impossibleByteCount =
    "System.Posix.IO.fdWriteBuf: returned a byte count greater than the length it was given"
-}


----------------------------------------------------------------
-- | Write a 'BL.ByteString' to an 'Fd'. This function makes a
-- single @writev(2)@ system call, as per 'PosixBS.fdWritev'.
fdWritev
    :: Fd
    -> BL.ByteString -- ^ The string to write.
    -> IO ByteCount  -- ^ How many bytes were actually written.
fdWritev fd s = PosixBS.fdWritev fd (BL.toChunks s)
{-# INLINE fdWritev #-}
-- Hopefully the intermediate list can be fused away...


----------------------------------------------------------------
----------------------------------------------------------- fin.
