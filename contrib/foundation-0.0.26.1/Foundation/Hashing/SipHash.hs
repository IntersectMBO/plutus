-- |
-- Module      : Foundation.Hashing.SipHash
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : good
--
-- provide the SipHash algorithm.
-- reference: <http://131002.net/siphash/siphash.pdf>
--
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
module Foundation.Hashing.SipHash
    ( SipKey(..)
    , SipHash(..)
    , Sip1_3
    , Sip2_4
    ) where

import           Data.Bits
import           Basement.Compat.Base
import           Basement.Types.OffsetSize
import           Basement.PrimType
import           Basement.Cast (cast)
import           Basement.IntegralConv
import           Foundation.Hashing.Hasher
import           Basement.Block (Block(..))
import qualified Basement.UArray as A
import           Foundation.Array
import           Foundation.Numerical
import           Foundation.Bits
import qualified Prelude
import           GHC.ST

-- | SigHash Key
data SipKey = SipKey {-# UNPACK #-} !Word64
                     {-# UNPACK #-} !Word64

-- | Siphash Hash value
newtype SipHash = SipHash Word64
    deriving (Show,Eq,Ord)

-- | Sip State 2-4 (2 compression rounds, 4 digest rounds)
newtype Sip2_4 = Sip2_4 Sip

-- | Sip State 1-3 (1 compression rounds, 3 digest rounds)
newtype Sip1_3 = Sip1_3 Sip

instance Hasher Sip2_4 where
    type HashResult Sip2_4      = SipHash
    type HashInitParam Sip2_4   = SipKey
    hashNew                     = Sip2_4 $ newSipState (SipKey 0 0)
    hashNewParam key            = Sip2_4 $ newSipState key
    hashEnd (Sip2_4 st)         = finish 2 4 st
    hashMix8 w (Sip2_4 st)      = Sip2_4 $ mix8 2 w st
    hashMix32 w (Sip2_4 st)     = Sip2_4 $ mix32 2 w st
    hashMix64 w (Sip2_4 st)     = Sip2_4 $ mix64 2 w st
    hashMixBytes ba (Sip2_4 st) = Sip2_4 $ mixBa 2 ba st

instance Hasher Sip1_3 where
    type HashResult Sip1_3      = SipHash
    type HashInitParam Sip1_3   = SipKey
    hashNew                     = Sip1_3 $ newSipState (SipKey 0 0)
    hashNewParam key            = Sip1_3 $ newSipState key
    hashEnd (Sip1_3 st)         = finish 1 3 st
    hashMix8 w (Sip1_3 st)      = Sip1_3 $ mix8 1 w st
    hashMix32 w (Sip1_3 st)     = Sip1_3 $ mix32 1 w st
    hashMix64 w (Sip1_3 st)     = Sip1_3 $ mix64 1 w st
    hashMixBytes ba (Sip1_3 st) = Sip1_3 $ mixBa 1 ba st

data Sip = Sip !InternalState !SipIncremental !(CountOf Word8)

data InternalState = InternalState {-# UNPACK #-} !Word64
                                   {-# UNPACK #-} !Word64
                                   {-# UNPACK #-} !Word64
                                   {-# UNPACK #-} !Word64

data SipIncremental =
      SipIncremental0
    | SipIncremental1 {-# UNPACK #-} !Word64
    | SipIncremental2 {-# UNPACK #-} !Word64
    | SipIncremental3 {-# UNPACK #-} !Word64
    | SipIncremental4 {-# UNPACK #-} !Word64
    | SipIncremental5 {-# UNPACK #-} !Word64
    | SipIncremental6 {-# UNPACK #-} !Word64
    | SipIncremental7 {-# UNPACK #-} !Word64

newSipState :: SipKey -> Sip
newSipState (SipKey k0 k1) = Sip st SipIncremental0 0
  where
    st = InternalState (k0 `xor` 0x736f6d6570736575)
                       (k1 `xor` 0x646f72616e646f6d)
                       (k0 `xor` 0x6c7967656e657261)
                       (k1 `xor` 0x7465646279746573)

mix8Prim :: Int -> Word8 -> InternalState -> SipIncremental -> (InternalState, SipIncremental)
mix8Prim !c !w !ist !incremental =
    case incremental of
        SipIncremental7 acc -> (process c ist ((acc `unsafeShiftL` 8) .|. Prelude.fromIntegral w), SipIncremental0)
        SipIncremental6 acc -> doAcc SipIncremental7 acc
        SipIncremental5 acc -> doAcc SipIncremental6 acc
        SipIncremental4 acc -> doAcc SipIncremental5 acc
        SipIncremental3 acc -> doAcc SipIncremental4 acc
        SipIncremental2 acc -> doAcc SipIncremental3 acc
        SipIncremental1 acc -> doAcc SipIncremental2 acc
        SipIncremental0     -> (ist, SipIncremental1 $ Prelude.fromIntegral w)
  where
    doAcc constr acc =
        (ist , constr ((acc .<<. 8) .|. Prelude.fromIntegral w))

mix8 :: Int -> Word8 -> Sip -> Sip
mix8 !c !w (Sip ist incremental len) =
    case incremental of
        SipIncremental7 acc -> Sip (process c ist ((acc .<<. 8) .|. Prelude.fromIntegral w))
                                   SipIncremental0 (len+1)
        SipIncremental6 acc -> doAcc SipIncremental7 acc
        SipIncremental5 acc -> doAcc SipIncremental6 acc
        SipIncremental4 acc -> doAcc SipIncremental5 acc
        SipIncremental3 acc -> doAcc SipIncremental4 acc
        SipIncremental2 acc -> doAcc SipIncremental3 acc
        SipIncremental1 acc -> doAcc SipIncremental2 acc
        SipIncremental0     -> Sip ist (SipIncremental1 $ Prelude.fromIntegral w) (len+1)
  where
    doAcc constr acc =
        Sip ist (constr ((acc .<<. 8) .|. Prelude.fromIntegral w)) (len+1)

mix32 :: Int -> Word32 -> Sip -> Sip
mix32 !c !w (Sip ist incremental len) =
    case incremental of
        SipIncremental0     -> Sip ist (SipIncremental4 $ Prelude.fromIntegral w) (len+4)
        SipIncremental1 acc -> consume acc 32 SipIncremental5
        SipIncremental2 acc -> consume acc 32 SipIncremental6
        SipIncremental3 acc -> consume acc 32 SipIncremental7
        SipIncremental4 acc -> Sip (process c ist ((acc .<<. 32) .|. Prelude.fromIntegral w)) SipIncremental0 (len+4)
        SipIncremental5 acc -> consumeProcess acc 24 8 SipIncremental1
        SipIncremental6 acc -> consumeProcess acc 16 16 SipIncremental2
        SipIncremental7 acc -> consumeProcess acc  8 24 SipIncremental3
  where
    consume acc n constr =
        Sip ist (constr ((acc .<<. n) .&. Prelude.fromIntegral w)) (len+4)
    {-# INLINE consume #-}
    consumeProcess acc n x constr =
        Sip (process c ist ((acc .<<. n) .|. (Prelude.fromIntegral w .>>. x)))
            (constr (Prelude.fromIntegral w .&. andMask64 n))
            (len+4)
    {-# INLINE consumeProcess #-}

mix64 :: Int -> Word64 -> Sip -> Sip
mix64 !c !w (Sip ist incremental len) =
    case incremental of
        SipIncremental0     -> Sip (process c ist w) SipIncremental0 (len+8)
        SipIncremental1 acc -> consume acc 56 8 SipIncremental1
        SipIncremental2 acc -> consume acc 48 16 SipIncremental2
        SipIncremental3 acc -> consume acc 40 24 SipIncremental3
        SipIncremental4 acc -> consume acc 32 32 SipIncremental4
        SipIncremental5 acc -> consume acc 24 40 SipIncremental5
        SipIncremental6 acc -> consume acc 16 48 SipIncremental6
        SipIncremental7 acc -> consume acc  8 56 SipIncremental7
  where
    consume acc n x constr =
        Sip (process c ist ((acc .<<. n) .|. ((w .>>. x) .&. andMask64 n)))
            (constr $ acc .&. andMask64 x)
            (len+8)
    {-# INLINE consume #-}

finish :: Int -> Int -> Sip -> SipHash
finish !c !d (Sip ist incremental (CountOf len)) = finalize d $
    case incremental of
        SipIncremental0     -> process c ist lenMask
        SipIncremental1 acc -> process c ist (lenMask .|. acc)
        SipIncremental2 acc -> process c ist (lenMask .|. acc)
        SipIncremental3 acc -> process c ist (lenMask .|. acc)
        SipIncremental4 acc -> process c ist (lenMask .|. acc)
        SipIncremental5 acc -> process c ist (lenMask .|. acc)
        SipIncremental6 acc -> process c ist (lenMask .|. acc)
        SipIncremental7 acc -> process c ist (lenMask .|. acc)
  where
    lenMask = (wlen .&. 0xff) .<<. 56
    wlen = cast (integralUpsize len :: Int64) :: Word64

-- | same as 'hash', except also specifies the number of sipround iterations for compression (C) and digest (D).
mixBa :: PrimType a => Int -> UArray a -> Sip -> Sip
mixBa !c !array (Sip initSt initIncr currentLen) =
    A.unsafeDewrap goVec goAddr array8
  where
    totalLen = A.length array8
    array8 = A.unsafeRecast array

    goVec :: Block Word8 -> Offset Word8 -> Sip
    goVec (Block ba) start = loop8 initSt initIncr start totalLen
      where
        loop8 !st !incr            _     0 = Sip st incr (currentLen + totalLen)
        loop8 !st SipIncremental0 !ofs !l = case l - 8 of
            Nothing -> loop1 st SipIncremental0 ofs l
            Just l8 ->
                let v =     to64 56 (primBaIndex ba ofs)
                        .|. to64 48 (primBaIndex ba (ofs + Offset 1))
                        .|. to64 40 (primBaIndex ba (ofs + Offset 2))
                        .|. to64 32 (primBaIndex ba (ofs + Offset 3))
                        .|. to64 24 (primBaIndex ba (ofs + Offset 4))
                        .|. to64 16 (primBaIndex ba (ofs + Offset 5))
                        .|. to64 8  (primBaIndex ba (ofs + Offset 6))
                        .|. to64 0  (primBaIndex ba (ofs + Offset 7))
                in loop8 (process c st v) SipIncremental0 (start + Offset 8) l8
        loop8 !st !incr !ofs !l = loop1 st incr ofs l
        loop1 !st !incr !ofs !l = case l - 1 of
            Nothing -> Sip st incr (currentLen + totalLen)
            Just l1 -> let (!st', !incr') = mix8Prim c (primBaIndex ba ofs) st incr
                        in loop1 st' incr' (ofs + Offset 1) l1

    to64 :: Int -> Word8 -> Word64
    to64 0  !v = Prelude.fromIntegral v
    to64 !s !v = Prelude.fromIntegral v .<<. s

    goAddr :: Ptr Word8 -> Offset Word8 -> ST s Sip
    goAddr (Ptr ptr) start = return $ loop8 initSt initIncr start totalLen
      where
        loop8 !st !incr            _     0 = Sip st incr (currentLen + totalLen)
        loop8 !st SipIncremental0 !ofs !l = case l - 8 of
            Nothing -> loop1 st SipIncremental0 ofs l
            Just l8 ->
                let v =     to64 56 (primAddrIndex ptr ofs)
                        .|. to64 48 (primAddrIndex ptr (ofs + Offset 1))
                        .|. to64 40 (primAddrIndex ptr (ofs + Offset 2))
                        .|. to64 32 (primAddrIndex ptr (ofs + Offset 3))
                        .|. to64 24 (primAddrIndex ptr (ofs + Offset 4))
                        .|. to64 16 (primAddrIndex ptr (ofs + Offset 5))
                        .|. to64 8  (primAddrIndex ptr (ofs + Offset 6))
                        .|. to64 0  (primAddrIndex ptr (ofs + Offset 7))
                in loop8 (process c st v) SipIncremental0 (start + Offset 8) l8 -- (l - 8)
        loop8 !st !incr !ofs !l = loop1 st incr ofs l
        loop1 !st !incr !ofs !l = case l - 1 of
          Nothing -> Sip st incr (currentLen + totalLen)
          Just l1 -> let (!st', !incr') = mix8Prim c (primAddrIndex ptr ofs) st incr
                      in loop1 st' incr' (ofs + Offset 1) l1

doRound :: InternalState -> InternalState
doRound (InternalState !v0 !v1 !v2 !v3) =
      let !v0'    = v0 + v1
          !v2'    = v2 + v3
          !v1'    = v1 `rotateL` 13
          !v3'    = v3 `rotateL` 16
          !v1''   = v1' `xor` v0'
          !v3''   = v3' `xor` v2'
          !v0''   = v0' `rotateL` 32
          !v2''   = v2' + v1''
          !v0'''  = v0'' + v3''
          !v1'''  = v1'' `rotateL` 17
          !v3'''  = v3'' `rotateL` 21
          !v1'''' = v1''' `xor` v2''
          !v3'''' = v3''' `xor` v0'''
          !v2'''  = v2'' `rotateL` 32
       in InternalState v0''' v1'''' v2''' v3''''
{-# INLINE doRound #-}

process :: Int -> InternalState -> Word64 -> InternalState
process !c !istate !m = postInject $! runRoundsCompression $! preInject istate
  where
    preInject  (InternalState v0 v1 v2 v3) = InternalState v0 v1 v2 (v3 `xor` m)
    postInject (InternalState v0 v1 v2 v3) = InternalState (v0 `xor` m) v1 v2 v3

    runRoundsCompression st
        | c == 2    = doRound $! doRound st
        | otherwise = loopRounds c st
{-# INLINE process #-}

finalize :: Int -> InternalState -> SipHash
finalize !d !istate = getDigest $! runRoundsDigest $! preInject istate
  where
    getDigest (InternalState v0 v1 v2 v3) = SipHash (v0 `xor` v1 `xor` v2 `xor` v3)
    preInject (InternalState v0 v1 v2 v3) = InternalState v0 v1 (v2 `xor` 0xff) v3
    runRoundsDigest st
        | d == 4    = doRound $! doRound $! doRound $! doRound st
        | otherwise = loopRounds d st
{-# INLINE finalize #-}

loopRounds :: Int -> InternalState -> InternalState
loopRounds 1 !v = doRound v
loopRounds n !v = loopRounds (n-1) (doRound v)
{-# INLINE loopRounds #-}

andMask64 :: Int -> Word64
andMask64 64 = 0xffffffffffffffff
andMask64 56 = 0x00ffffffffffffff
andMask64 48 = 0x0000ffffffffffff
andMask64 40 = 0x000000ffffffffff
andMask64 32 = 0x00000000ffffffff
andMask64 24 = 0x0000000000ffffff
andMask64 16 = 0x000000000000ffff
andMask64 8  = 0x00000000000000ff
andMask64 n  = (1 .<<. n) - (1 :: Word64)
{-# INLINE andMask64 #-}
