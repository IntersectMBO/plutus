module Language.Marlowe.Deserialisation (byteStringToPositiveInt, getByteString, byteStringToInt, byteStringToList) where

import           PlutusTx.Builtins (BuiltinByteString, divideInteger, indexByteString, lengthOfByteString,
                                    sliceByteString)

{-# INLINABLE unconsByte #-}
-- | @unconsByte bs@ returns a tuple where the first element is the first byte
-- of @bs@ (represented as a number from 0 to 255), and the second element is
-- the remainder of @bs@, if @bs@ is empty it returns @Nothing@.
unconsByte :: BuiltinByteString -> Maybe (Integer, BuiltinByteString)
unconsByte bs = let bsLength = lengthOfByteString bs in
                if bsLength < 1
                then Nothing
                else let firstByte = indexByteString bs 0
                         remainingBs = sliceByteString 1 bsLength bs in
                         Just (firstByte, remainingBs)

{-# INLINABLE splitByteStringAt #-}
-- | @splitByteStringAt n bs@ returns a tuple where first element is @bs@ prefix of length @n@
-- and second element is the remainder of @bs@.
splitByteStringAt :: Integer -> BuiltinByteString -> (BuiltinByteString, BuiltinByteString)
splitByteStringAt n bs = (sliceByteString 0 n bs, sliceByteString n (lengthOfByteString bs) bs)

{-# INLINABLE byteStringToPositiveInt #-}
-- | @byteStringToPositiveInt bs@ tries to read a non-negative integer of arbitrary size from the
-- beginning of @bs@ and it returns a tuple with the integer as the first element, and the remainder
-- of @bs@ as a second element. If @bs@ does not contain a complete representation of a non-negative
-- integer @byteStringToPositiveInt@ returns @Nothing@.
byteStringToPositiveInt :: BuiltinByteString -> Maybe (Integer, BuiltinByteString)
byteStringToPositiveInt bs =
  case unconsByte bs of
    Nothing -> Nothing
    Just (x, rest) ->
        (if x < 128
         then Just (x, rest)
         else (case byteStringToPositiveInt rest of
                Nothing -> Nothing
                Just (y, extra) ->
                  Just ((x - 128) + (128 * (y + 1)), extra)))

{-# INLINABLE getByteString #-}
-- | @getByteString bs@ extracts a length-prefixed string from the beginning of @bs@, and
-- it returns it as the first element of a tuple and the remainder of @bs@ as the second
-- element of the tuple. If the beginning of @bs@ does not correspond to a lenght-prefixed
-- string then @getByteString@ returns @Nothing@.
getByteString :: BuiltinByteString -> Maybe (BuiltinByteString, BuiltinByteString)
getByteString bs =
  case byteStringToPositiveInt bs of
   Nothing -> Nothing
   Just (val, rest) ->
     (if lengthOfByteString rest < val
      then Nothing
      else Just (splitByteStringAt val rest))

{-# INLINABLE byteStringToInt #-}
-- | @byteStringToPositiveInt bs@ tries to read an integer of arbitrary size from the beginning
-- of @bs@ and it returns a tuple with the integer as the first element, and the remainder
-- of @bs@ as a second element. If @bs@ does not contain a complete representation of an integer
-- number @byteStringToPositiveInt@ returns @Nothing@.
byteStringToInt :: BuiltinByteString -> Maybe (Integer, BuiltinByteString)
byteStringToInt x =
  case byteStringToPositiveInt x of
   Nothing -> Nothing
   Just (y, extra) ->
     Just (if even y
           then y `divideInteger` 2
           else 0 - (y `divideInteger` 2 + 1), extra)

{-# INLINABLE byteStringToListAux #-}
byteStringToListAux :: (BuiltinByteString -> Maybe (a, BuiltinByteString)) -> Integer -> BuiltinByteString -> Maybe ([a], BuiltinByteString)
byteStringToListAux f n bs =
  if 0 < n
  then case f bs of
          Nothing -> Nothing
          Just (aa, nbs) -> case byteStringToListAux f (n - 1) nbs of
                              Nothing        -> Nothing
                              Just (lr, fbs) -> Just (aa : lr, fbs)
   else Just ([], bs)

{-# INLINABLE byteStringToList #-}
-- | @byteStringToList f bs@ deserialises a list of elements such that each of the elements
-- can be deserialised by the function @f@, and obtains them from the beginning of @bs@.
-- @byteStringToList@ returns a tuple where the first element of the tuple is the list of
-- deserialised elements of the list, and the second element is the remaining of @bs@.
-- If the beginning of @bs@ does not correspond to a serialised list of elements that can
-- be deserialised by the function @f@ it returns @Nothing@.
byteStringToList :: (BuiltinByteString -> Maybe (a, BuiltinByteString)) -> BuiltinByteString -> Maybe ([a], BuiltinByteString)
byteStringToList f bs = case byteStringToPositiveInt bs of
                         Nothing      -> Nothing
                         Just (aa, b) -> byteStringToListAux f aa b

