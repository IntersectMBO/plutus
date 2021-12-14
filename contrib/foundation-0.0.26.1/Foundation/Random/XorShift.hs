-- |
-- Module      : Foundation.Random.XorShift
-- License     : BSD-style
--
-- XorShift variant: Xoroshiro128+
-- <https://en.wikipedia.org/wiki/Xoroshiro128%2B>
--
-- C implementation at:
-- <http://xoroshiro.di.unimi.it/xoroshiro128plus.c>
--
{-# LANGUAGE MagicHash #-}
module Foundation.Random.XorShift
    ( State
    , initialize
    , next
    , nextList
    , nextDouble
    ) where

import           Basement.Imports
import           Basement.PrimType
import           Basement.Types.OffsetSize
import           Foundation.Numerical
import           Foundation.Bits
import           Foundation.Random.Class
import           Foundation.Random.DRG
import           Basement.Compat.Bifunctor
import           Basement.Compat.ExtList (reverse)
import qualified Basement.UArray as A
import qualified Prelude
import           GHC.Prim
import           GHC.Float


-- | State of Xoroshiro128 plus
data State = State {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64

instance RandomGen State where
    randomNew = initialize <$> getRandomWord64 <*> getRandomWord64
    randomNewFrom bs
        | A.length bs == 16 =
            let bs64 = A.recast bs
             in Just $ State (A.index bs64 0) (A.index bs64 1)
        | otherwise         = Nothing
    randomGenerate = generate
    randomGenerateWord64 = next
    randomGenerateF32 = nextFloat
    randomGenerateF64 = nextDouble

initialize :: Word64 -> Word64 -> State
initialize s0 s1 = State s0 s1

generate :: CountOf Word8 -> State -> (UArray Word8, State)
generate c st =
    first (A.take c . A.unsafeRecast . fromList) $ nextList c64 st
  where
    c64 = sizeRecast c'
    c' = countOfRoundUp 8 c

next :: State -> (Word64, State)
next (State s0 s1prev) = (s0 + s1prev, State s0' s1')
  where
    !s1 = s0 `xor` s1prev
    s0' = (s0 `rotateL` 55) `xor` s1 `xor` (s1 .<<. 14)
    s1' = (s1 `rotateL` 36)

nextList :: CountOf Word64 -> State -> ([Word64], State)
nextList c state = loop [] state 0
  where
    loop acc st o
        | o .==# c  = (reverse acc, st)
        | otherwise =
            let (w, st') = next st
             in loop (w:acc) st' (o+1)

nextFloat :: State -> (Float, State)
nextFloat = first dToF . nextDouble
  where dToF (D# d) = F# (double2Float# d)

nextDouble :: State -> (Double, State)
nextDouble !st = (d' - 1.0 , st')
  where
    !(w, st') = next st
    upperMask = 0x3FF0000000000000
    lowerMask = 0x000FFFFFFFFFFFFF
    d' :: Double
    d' = Prelude.fromIntegral d
    d = upperMask .|. (w .&. lowerMask)
