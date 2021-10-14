-----------------------------------------------------------------------------
-- |
-- Module      :  Languge.Marlowe.Serialisation
--
-- This module provides provisional building blocks for serialising
-- algebraic datatypes in Plutus for completeness and testing purpouses.
--
-- Currently these functions are very inefficient so they should not
-- be used in on-chain code.
--
-----------------------------------------------------------------------------

module Language.Marlowe.Serialisation(positiveIntToByteString, packByteString, intToByteString, listToByteString) where

import           PlutusTx.Builtins (BuiltinByteString, appendByteString, consByteString, divideInteger, emptyByteString,
                                    lengthOfByteString, modInteger)

{-# INLINABLE singletonByteString #-}
-- | @singletonByteString n@ returns a single-byte 'BuiltinByteString' with the byte represented by
-- the number @n@ (that must be between 0 and 255).
singletonByteString :: Integer -> BuiltinByteString
singletonByteString n = consByteString n emptyByteString

{-# INLINABLE positiveIntToByteString #-}
-- | Serialises a non-negative integer of arbitrary size into a 'BuiltinByteString'.
positiveIntToByteString :: Integer -> BuiltinByteString
positiveIntToByteString x =
  if x < 128 then singletonByteString x
  else consByteString (x `modInteger` 128 + 128) $
          positiveIntToByteString (x `divideInteger` 128 - 1)

{-# INLINABLE packByteString #-}
-- | Converts a 'BuiltinByteString' into a length-prefixed 'BuiltinByteString'.
packByteString :: BuiltinByteString -> BuiltinByteString
packByteString bs = positiveIntToByteString (lengthOfByteString bs) `appendByteString` bs

{-# INLINABLE intToByteString #-}
-- | Serialises an integer of arbitrary size into a 'BuiltinByteString'.
intToByteString :: Integer -> BuiltinByteString
intToByteString x =
   if 0 <= x
   then positiveIntToByteString (x * 2)
   else positiveIntToByteString (0 - (x * 2 + 1))

{-# INLINABLE listToByteString #-}
-- | @listToByteString f l@ Serialises the list of elements @l@ such that each of
-- the elements of @l@ can be serialised using the function @f@.
listToByteString :: (a -> BuiltinByteString) -> [a] -> BuiltinByteString
listToByteString f l =
  positiveIntToByteString (fromIntegral $ length l) `appendByteString` listToByteStringAux f l
  where listToByteStringAux :: (a -> BuiltinByteString) -> [a] -> BuiltinByteString
        listToByteStringAux f' = foldr (appendByteString . f') mempty

