-- |
-- Module      : Foundation.Timing
-- License     : BSD-style
-- Maintainer  : Foundation maintainers
--
-- An implementation of a timing framework
--
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foundation.Time.Types
    ( NanoSeconds(..)
    , Seconds(..)
    ) where

import           Data.Proxy
import           Basement.Imports
import           Basement.PrimType
import           Foundation.Numerical
import           Data.Coerce

-- | An amount of nanoseconds
newtype NanoSeconds = NanoSeconds Word64
    deriving (Show,Eq,Ord,Additive,Enum,Bounded)


instance PrimType NanoSeconds where
    type PrimSize NanoSeconds = 8
    primSizeInBytes _        = primSizeInBytes (Proxy :: Proxy Word64)
    primShiftToBytes _       = primShiftToBytes (Proxy :: Proxy Word64)
    primBaUIndex ba ofs      = primBaUIndex ba (coerce ofs)
    primMbaURead mba ofs     = primMbaURead mba (coerce ofs)
    primMbaUWrite mba ofs v  = primMbaUWrite mba (coerce ofs) (coerce v :: Word64)
    primAddrIndex addr ofs   = primAddrIndex addr (coerce ofs)
    primAddrRead addr ofs    = primAddrRead addr (coerce ofs)
    primAddrWrite addr ofs v = primAddrWrite addr (coerce ofs) (coerce v :: Word64)

-- | An amount of seconds
newtype Seconds = Seconds Word64
    deriving (Show,Eq,Ord,Additive,Enum,Bounded)

instance PrimType Seconds where
    type PrimSize Seconds    = 8
    primSizeInBytes _        = primSizeInBytes (Proxy :: Proxy Word64)
    primShiftToBytes _       = primShiftToBytes (Proxy :: Proxy Word64)
    primBaUIndex ba ofs      = primBaUIndex ba (coerce ofs)
    primMbaURead mba ofs     = primMbaURead mba (coerce ofs)
    primMbaUWrite mba ofs v  = primMbaUWrite mba (coerce ofs) (coerce v :: Word64)
    primAddrIndex addr ofs   = primAddrIndex addr (coerce ofs)
    primAddrRead addr ofs    = primAddrRead addr (coerce ofs)
    primAddrWrite addr ofs v = primAddrWrite addr (coerce ofs) (coerce v :: Word64)
