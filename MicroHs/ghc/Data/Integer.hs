module Data.Integer(_integerToIntList) where

-- Same as in Data.Integer
_integerToIntList :: Integer -> [Int]
_integerToIntList i | i < 0 = -1 : to (-i)
                    | otherwise =  to i
  where to 0 = []
        to n = fromInteger r : to q  where (q, r) = quotRem n 32768
