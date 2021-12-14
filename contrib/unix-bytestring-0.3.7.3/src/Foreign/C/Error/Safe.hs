
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2012.02.21
-- |
-- Module      :  Foreign.C.Error.Safe
-- Copyright   :  Copyright (c) 2010--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  provisional
-- Portability :  portable (H98+FFI)
--
-- Provides a variant of the "Foreign.C.Error" API which returns
-- errors explicitly, instead of throwing exceptions.
--
-- /Since: 0.3.5/
----------------------------------------------------------------
module Foreign.C.Error.Safe
    (
    -- * Primitive handlers
      eitherErrnoIf
    , eitherErrnoIfRetry
    , eitherErrnoIfRetryMayBlock
    -- * Derived handlers
    -- ** With predicate @(-1 ==)@
    , eitherErrnoIfMinus1
    , eitherErrnoIfMinus1Retry
    , eitherErrnoIfMinus1RetryMayBlock
    -- ** With predicate @(nullPtr ==)@
    , eitherErrnoIfNull
    , eitherErrnoIfNullRetry
    , eitherErrnoIfNullRetryMayBlock
    ) where

import qualified Foreign.C.Error as C
import qualified Foreign.Ptr     as FFI

----------------------------------------------------------------
----------------------------------------------------------------

-- | A variant of 'C.throwErrnoIf' which returns @Either@ instead
-- of throwing an errno error.
eitherErrnoIf
    :: (a -> Bool)  -- ^ Predicate to apply to the result value of
                    --   the @IO@ operation.
    -> IO a         -- ^ The @IO@ operation to be executed.
    -> IO (Either C.Errno a)
eitherErrnoIf p io = do
    a <- io
    if p a
        then do
            errno <- C.getErrno
            return (Left errno)
        else return (Right a)


-- | A variant of 'C.throwErrnoIfRetry' which returns @Either@
-- instead of throwing an errno error.
eitherErrnoIfRetry
    :: (a -> Bool)  -- ^ Predicate to apply to the result value of
                    --   the @IO@ operation.
    -> IO a         -- ^ The @IO@ operation to be executed.
    -> IO (Either C.Errno a)
eitherErrnoIfRetry p io = loop
    where
    loop = do
        a <- io
        if p a
            then do
                errno <- C.getErrno
                if errno == C.eINTR
                    then loop
                    else return (Left errno)
            else return (Right a)


-- | A variant of 'C.throwErrnoIfRetryMayBlock' which returns
-- @Either@ instead of throwing an errno error.
eitherErrnoIfRetryMayBlock
    :: (a -> Bool)  -- ^ Predicate to apply to the result value of
                    --   the @IO@ operation.
    -> IO a         -- ^ The @IO@ operation to be executed.
    -> IO b         -- ^ Action to execute before retrying if an
                    --   immediate retry would block.
    -> IO (Either C.Errno a)
eitherErrnoIfRetryMayBlock p f on_block = loop
    where
    loop = do
        a <- f
        if p a
            then do
                errno <- C.getErrno
                if errno == C.eINTR
                    then loop
                    else if errno == C.eWOULDBLOCK || errno == C.eAGAIN
                         then on_block >> loop
                         else return (Left errno)
            else return (Right a)

----------------------------------------------------------------

eitherErrnoIfMinus1 :: (Eq a, Num a) => IO a -> IO (Either C.Errno a)
eitherErrnoIfMinus1 = eitherErrnoIf (-1 ==)

eitherErrnoIfMinus1Retry :: (Eq a, Num a) => IO a -> IO (Either C.Errno a)
eitherErrnoIfMinus1Retry = eitherErrnoIfRetry (-1 ==)

eitherErrnoIfMinus1RetryMayBlock
    :: (Eq a, Num a) => IO a -> IO b -> IO (Either C.Errno a)
eitherErrnoIfMinus1RetryMayBlock =
    eitherErrnoIfRetryMayBlock (-1 ==)


eitherErrnoIfNull :: IO (FFI.Ptr a) -> IO (Either C.Errno (FFI.Ptr a))
eitherErrnoIfNull = eitherErrnoIf (== FFI.nullPtr)

eitherErrnoIfNullRetry :: IO (FFI.Ptr a) -> IO (Either C.Errno (FFI.Ptr a))
eitherErrnoIfNullRetry = eitherErrnoIfRetry (== FFI.nullPtr)

eitherErrnoIfNullRetryMayBlock
    :: IO (FFI.Ptr a) -> IO b -> IO (Either C.Errno (FFI.Ptr a))
eitherErrnoIfNullRetryMayBlock =
    eitherErrnoIfRetryMayBlock (== FFI.nullPtr)

----------------------------------------------------------------
----------------------------------------------------------- fin.
