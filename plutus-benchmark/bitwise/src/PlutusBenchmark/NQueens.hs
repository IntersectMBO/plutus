-- editorconfig-checker-disable-file
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.NQueens (nqueens) where

import PlutusTx.Prelude

-- Based on Qiu, Zongyan (February 2002). "Bit-vector encoding of n-queen problem". ACM SIGPLAN Notices. 37 (2): 68–70
-- For simplicity, this only accepts multiples of 8 for the dimension (so 8, 16,
-- 24, etc): in all other cases it will return an empty list. Results are (row,
-- column) pairs.
nqueens :: Integer -> [(Integer, Integer)]
nqueens dim
  | dim < 8 = []
  | dim `remainder` 8 /= 0 = []
  | otherwise =
      let down = replicateByte bytesNeeded 0x00
          left = replicateByte bytesNeeded 0x00
          right = replicateByte bytesNeeded 0x00
       in go 0 0 down left right (replicateByte bytesNeeded 0xFF)
  where
    bytesNeeded :: Integer
    bytesNeeded = dim `quotient` 8
    go
      :: Integer
      -> Integer
      -> BuiltinByteString
      -> BuiltinByteString
      -> BuiltinByteString
      -> BuiltinByteString
      -> [(Integer, Integer)]
    go selectIx row down left right control
      | selectIx == dim = []
      | otherwise =
          -- In the original writeup, 0 in a position meant 'occupied'. However,
          -- this makes updates to the control vectors very annoying, because
          -- now we have to 'shift in' 1 bits, which costs us an extra two
          -- copies. We can reduce this by one by instead treating 0 as 'free'.
          -- Ideally, we would eliminate one more redundant copy, but this
          -- requires a select0 operation, which can't be implemented
          -- efficiently. However, given that these copies are per recursive
          -- call, we can save ourselves considerable effort by avoiding them.
          let available = selectByteString selectIx control
           in if
                | available == (-1) -> []
                | row == lastRow -> [(row, available)]
                | otherwise ->
                    let newDown = writeBit down available True
                        newLeft = shiftByteString (writeBit left available True) 1
                        newRight = shiftByteString (writeBit right available True) (-1)
                        newRow = row + 1
                        -- We 'hoist' the control vector as a parameter rather
                        -- than recomputing it every time we modify selectIx.
                        newControl = complementByteString . orByteString False newDown . orByteString False newLeft $ newRight
                     in case go 0 newRow newDown newLeft newRight newControl of
                          [] -> go (selectIx + 1) row down left right control
                          next -> (row, available) : next
    lastRow :: Integer
    lastRow = dim - 1
{-# INLINE nqueens #-}

-- Helpers

selectByteString :: Integer -> BuiltinByteString -> Integer
selectByteString which bs
  | which <= 0 = findFirstSetBit bs
  | otherwise =
      let i = selectByteString (which - 1) bs
       in if i == (-1)
            then (-1)
            else i + 1 + findFirstSetBit (shiftByteString bs $ negate (i + 1))
{-# INLINE selectByteString #-}

writeBit :: BuiltinByteString -> Integer -> Bool -> BuiltinByteString
writeBit bs i b = writeBits bs [i] b
{-# INLINE writeBit #-}
