{-# LANGUAGE RankNTypes #-}

module Main where

import Criterion.Main
import Criterion.Main.Options
import Criterion.Types
import Test.QuickCheck

--------------------
-- Scott Encoding --
--------------------

newtype SList a = SList (forall r . r -> (a -> SList a -> r) -> r)

nil :: SList a
nil = SList (\n c -> n)

cons :: a -> SList a -> SList a
cons x xs = SList (\n c -> c x xs)

instance (Show a) => Show (SList a) where
  show (SList l) = l "[]" (\x xs -> (show x) ++ ":" ++ (show xs))

headS :: SList a -> a
headS (SList l) = l undefined (\x xs -> x)

-- the call to headS should be inlined, I think, so it's okay.
headTailS :: SList a -> a
headTailS (SList l) = l undefined (\x xs -> headS xs)

sumS :: SList Int -> Int
sumS (SList l) = l 0 (\x xs -> x + (sumS xs))

appendS :: SList a -> SList a -> SList a
appendS (SList l1) l2 = l1 l2 (\x xs -> cons x (appendS xs l2))

filterS :: (a -> Bool) -> SList a -> SList a
filterS p (SList l) = l nil (\x xs -> if p x then cons x (filterS p xs) else (filterS p xs))

-- does cl@ have performance implications?
quickSortS :: (Ord a) => SList a -> SList a
quickSortS cl@(SList l) = l nil (\h t -> appendS (quickSortS (filterS (\x -> x < h) cl))
                                                 (appendS (filterS (\x -> x == h) cl)
                                                          (quickSortS (filterS (\x -> h < x) cl))))

fromList :: [a] -> SList a
fromList = foldr (\ x xs -> cons x xs) nil
-------------------
-- Builtin Lists --
-------------------

headTail :: [a] -> a
headTail []     = undefined
headTail (x:xs) = head xs

-- 'sum' is defined for Foldable things, and is significantly slower
-- than sumS, so a more comparable sum function is warranted.
directSum :: [Int] -> Int
directSum []     = 0
directSum (x:xs) = x + (directSum xs)

quickSort :: (Ord a) => [a] -> [a]
quickSort [] = []
quickSort cl@(h:xs) = (quickSort (filter (\x -> x < h) cl)) ++
                      (filter (\x -> x == h) cl) ++
                      (quickSort (filter (\x -> h < x) cl))

----------------
-- Benchmarks --
----------------

head_tail :: Benchmark
head_tail = bgroup "head_tail" [head_tail_scott,head_tail_builtin]

head_tail_scott :: Benchmark
head_tail_scott = bgroup "scott" (map (\m -> bench ("m = " ++ (show m))
                                                   (whnf headTailS (fromList [1..m] :: SList Int)))
                                      [2,10,10^2,10^3,10^4,10^5])

head_tail_builtin :: Benchmark
head_tail_builtin = bgroup "builtin" (map (\m -> bench ("m = " ++ (show m))
                                                       (whnf headTail ([1..m] :: [Int])))
                                          [2,10,10^2,10^3,10^4,10^5])

sum_ints :: Benchmark
sum_ints = bgroup "sum" [sum_ints_scott,sum_ints_builtin]

sum_ints_scott :: Benchmark
sum_ints_scott = bgroup "scott" (map (\m -> bench ("m = " ++ (show m))
                                                  (whnf sumS (fromList [1..m] :: SList Int)))
                                     [1,10,10^2,10^3,10^4,10^5,10^6,10^7])

sum_ints_builtin :: Benchmark
sum_ints_builtin = bgroup "builtin" (map (\m -> bench ("m = " ++ (show m))
                                                      (whnf directSum ([1..m] :: [Int])))
                                         [1,10,10^2,10^3,10^4,10^5,10^6,10^7])

quicksort_ints :: [(Int,[Int])] -> Benchmark
quicksort_ints = \testData -> bgroup "quicksort" [qs_scott testData,qs_builtin testData]

qs_scott :: [(Int,[Int])] -> Benchmark
qs_scott = \testData -> bgroup "scott" (map (\ (m,xs) -> bench ("m = " ++ (show m))
                                                                 (whnf quickSortS (fromList xs)))
                                        testData)

qs_builtin :: [(Int,[Int])] -> Benchmark
qs_builtin = \testData -> bgroup "builtin" (map (\ (m,xs) -> bench ("m = " ++ (show m))
                                                                     (whnf quickSort xs))
                                            testData)
main :: IO ()
main = do
    let g :: Gen [Int]
        g = infiniteListOf (elements [0..999])
    nums <- generate g
    let qs_data = map (\x -> (x,take x nums)) [1,10,10^2,10^3,10^4,10^5,10^6,10^7]
    defaultMainWith defaultConfig
                    [head_tail,sum_ints,quicksort_ints qs_data]

