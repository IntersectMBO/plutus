-- |
-- Module      : Foundation.Collection.List
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
module Foundation.Collection.List
    ( wordsWhen
    , revTake
    , revDrop
    , revSplitAt
    , breakEnd
    , uncons
    , unsnoc
    ) where

import qualified Data.List
import           Data.Tuple (swap)
import           Basement.Compat.Base
import           Foundation.Numerical

-- | Simple helper to split a list repeatly when the predicate match
wordsWhen     :: (x -> Bool) -> [x] -> [[x]]
wordsWhen _ [] = [[]]
wordsWhen p is = loop is
  where
    loop s =
        let (w, s') = Data.List.break p s
         in case s' of
                []   -> [w]
                _:xs -> w : loop xs

revTake :: Int -> [a] -> [a]
revTake n l = Data.List.drop (len - n) l
  where
    len = Data.List.length l

revDrop :: Int -> [a] -> [a]
revDrop n l = Data.List.take (len - n) l
  where
    len = Data.List.length l

revSplitAt :: Int -> [a] -> ([a],[a])
revSplitAt n l = swap $ Data.List.splitAt (len - n) l
  where
    len = Data.List.length l

breakEnd :: (a -> Bool) -> [a] -> ([a], [a])
breakEnd predicate l =
    let (l1,l2) = Data.List.break predicate (Data.List.reverse l)
     in if Data.List.null l2 then (l, []) else (Data.List.reverse l2, Data.List.reverse l1)

uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

unsnoc :: [a] -> Maybe ([a], a)
unsnoc []       = Nothing
unsnoc [x]      = Just ([], x)
unsnoc [x,y]    = Just ([x], y)
unsnoc (x:xs@(_:_)) = Just $ loop [x] xs
  where
    loop acc [y]    = (Data.List.reverse acc, y)
    loop acc (y:ys) = loop (y:acc) ys
    loop _   _      = error "impossible"
