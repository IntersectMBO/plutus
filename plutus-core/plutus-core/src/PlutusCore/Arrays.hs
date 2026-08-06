{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Implementation for the array builtins of CIP-0156 that needs more than a one-liner.
module PlutusCore.Arrays
  ( multiIndexArray
  , maximumIndexCount
  ) where

import PlutusCore.Builtin.Result (BuiltinResult, builtinResultFailure, emit)

import Data.Text (pack)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector

{- Note [Index count limitation for multiIndexArray]
Looking up a list of indices means walking that list, and the time to walk a
list is not determined by its length alone, so execution time stops being
predictable from the index count beyond some size.  We therefore limit the
number of indices, and the cost model is fitted over exactly that range.  The
limit is far above any realistic use: a transaction is limited to 16384 bytes,
so a serialised list of this many indices would not fit even if the transaction
carried nothing else.  This limit may be raised once costing can bound the cost
without it, but note that doing so would need a second variant of the builtin so
that existing scripts keep their current behaviour.

Compare Note [Input length limitation for IntegerToByteString], which limits
those builtins for the same underlying reason.

The count is checked during the traversal rather than up front, because taking
the length first would walk the list twice. -}
maximumIndexCount :: Int
maximumIndexCount = 4096
{-# INLINE maximumIndexCount #-}

{-| Look up every index of the given list in the given array.

Fails if any index is out of bounds, or if there are more than
'maximumIndexCount' of them; see Note [Index count limitation for
multiIndexArray].

The elements are read eagerly, as in @indexArray@, so that the read is paid for
inside this builtin rather than wherever the element is later demanded.  Forcing
is safe: the vector is strict, so the element is already in normal form as far
as this function is concerned. -}
multiIndexArray :: forall a. Vector a -> [Integer] -> BuiltinResult [a]
multiIndexArray vec = go 0
  where
    !len = toInteger (Vector.length vec)

    go :: Int -> [Integer] -> BuiltinResult [a]
    go !_ [] = pure []
    go !n (i : is)
      | n >= maximumIndexCount = do
          emit . pack $
            "multiIndexArray: too many indices (maximum is "
              ++ show maximumIndexCount
              ++ ")"
          builtinResultFailure
      | 0 <= i && i < len = do
          let !x = Vector.unsafeIndex vec (fromInteger i)
          (x :) <$> go (n + 1) is
      | otherwise = do
          emit "multiIndexArray: array index out of bounds"
          emit $ "Index: " <> (pack . show $ i)
          builtinResultFailure
{-# INLINE multiIndexArray #-}
