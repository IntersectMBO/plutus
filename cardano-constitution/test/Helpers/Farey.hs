-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

module Helpers.Farey (findTightestRationalBounds, Digits) where

import Data.Ratio ((%))

goLeftInFsbTree
  :: Integer
  -> Integer
  -> Integer
  -> Integer
  -> (Integer, Integer, Integer, Integer)
goLeftInFsbTree a b c d =
  let (e, f) = (c, d)
      (c', d') = (a + c, b + d)
   in (c', d', e, f)

goRightInFsbTree
  :: Integer
  -> Integer
  -> Integer
  -> Integer
  -> (Integer, Integer, Integer, Integer)
goRightInFsbTree c d e f =
  let (a, b) = (c, d)
      (c', d') = (c + e, d + f)
   in (a, b, c', d')

findFsbSubtree
  :: Rational
  -> Integer
  -> (Integer, Integer, Integer, Integer, Integer, Integer)
findFsbSubtree target limNumb =
  let (a, b, c, d, e, f) = (0, 1, 1, 1, 1, 0)
   in loop a b c d e f
  where
    loop a b c d e f
      | c % d == target || any (>= limNumb) [a, b, c, d, e, f] = (a, b, c, d, e, f)
      | a % b < target && target < c % d =
          let (c', d', e', f') = goLeftInFsbTree a b c d
           in loop a b c' d' e' f'
      | otherwise =
          let (a', b', c', d') = goRightInFsbTree c d e f
           in loop a' b' c' d' e f

findSuccInFsbTree
  :: (Integer, Integer, Integer, Integer)
  -> Integer
  -> (Integer, Integer)
findSuccInFsbTree (c, d, e, f) limNumb =
  -- The successors are in the right subtree, the smallest one is the leftmost leaf
  let (a, b, c', d') = goRightInFsbTree c d e f
      -- Replaced the iterative go_left with a single step since it follows an arithmetic progression
      n_d = (limNumb - d') `div` b
      n_c = (limNumb - c') `div` a
      n = min n_d n_c
   in (c' + n * a, d' + n * b)

findPredInFsbTree
  :: (Integer, Integer, Integer, Integer)
  -> Integer
  -> (Integer, Integer)
findPredInFsbTree (a, b, c, d) limNumb =
  -- The predecessors are in the left subtree, the smallest one is the rightmost leaf
  let (c', d', e, f) = goLeftInFsbTree a b c d
      -- Replaced the iterative go_right with a single step since it follows an arithmetic progression
      n_d = (limNumb - d') `div` f
      n_c = (limNumb - c') `div` e
      n = min n_d n_c
   in (c' + n * e, d' + n * f)

findTightestRationalBounds'
  :: Bool
  -> Rational
  -> Integer
  -> (Rational, Rational)
findTightestRationalBounds' flipped target limNumb =
  case compare target 0 of
    EQ -> (-1 % limNumb, 1 % limNumb)
    LT -> findTightestRationalBounds' True (abs target) limNumb
    _anyOther ->
      let (a, b, c, d, e, f) = findFsbSubtree target limNumb
          (p_n, p_d) = findPredInFsbTree (a, b, c, d) limNumb
          (s_n, s_d) = findSuccInFsbTree (c, d, e, f) limNumb
       in if flipped
            then (-s_n % s_d, -p_n % p_d)
            else (p_n % p_d, s_n % s_d)

type Digits = Int
findTightestRationalBounds :: Rational -> Digits -> (Rational, Rational)
findTightestRationalBounds ratio digits = findTightestRationalBounds' False ratio (2 ^ digits - 1)

-- >>> findTightestRationalBounds (17 % 20) 64
-- (15679732462653118871 % 18446744073709551613,15679732462653118866 % 18446744073709551607)

-- >>> findTightestRationalBounds (17 % 20) 4
-- (11 % 13,6 % 7)

-- >>> findTightestRationalBounds (1 % 20) 1
-- Ratio has zero denominator
