{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedSums #-}
module GHC.Num.Integer.Extras where

import GHC.Prim
import GHC.Types
import GHC.Num.Integer
import GHC.Num.BigNat

-- | Truncates 'Integer' to least-significant 'Int#'
integerToIntMaybe :: Integer -> Maybe Int
integerToIntMaybe (IS i) = Just (I# i)
integerToIntMaybe (IP b)
   | (# | m' #) <- bigNatToWordMaybe# b = Just (I# (word2Int# m'))
integerToIntMaybe (IN b)
   | (# | m' #) <- bigNatToWordMaybe# b = Just (I# (negateInt# (word2Int# m')))
integerToIntMaybe _ = Nothing
