{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module Helpers.Intervals where

import Control.Monad (guard)
import Data.List
import Helpers.TestBuilders hiding (rangeGen)
import Test.QuickCheck (Gen, oneof, suchThat)

--------------------------------------------------------------------------------
-- | Boundaries
data Boundary a = Closed !a | Open !a
  deriving stock (Show, Eq)

boundaryValue :: Boundary a -> a
boundaryValue (Closed a) = a
boundaryValue (Open a) = a

instance (Num a, Ord a) => Ord (Boundary a) where
  compare (boundaryValue -> a) (boundaryValue -> b)
    | a /= b = compare a b
  compare (Open a) (Closed _) = 0 `compare` a
  compare (Closed a) (Open _) = a `compare` 0
  compare (Open _) (Open _) = EQ
  compare (Closed _) (Closed _) = EQ

--------------------------------------------------------------------------------
-- | Ranges
data RangeConstraint a = NL !a | NG !a | NLEQ !a | NGEQ !a | NEQ !a
  deriving stock (Show, Eq)

rangeValue :: RangeConstraint a -> a
rangeValue (NL a) = a
rangeValue (NG a) = a
rangeValue (NLEQ a) = a
rangeValue (NGEQ a) = a
rangeValue (NEQ a) = a

type Interval a = (Boundary a, Boundary a)

showInterval :: Show a => Interval a -> String
showInterval (Closed a, Closed b) = "[" <> show a <> ", " <> show b <> "]"
showInterval (Open a, Open b) = "(" <> show a <> ", " <> show b <> ")"
showInterval (Open a, Closed b) = "(" <> show a <> ", " <> show b <> "]"
showInterval (Closed a, Open b) = "[" <> show a <> ", " <> show b <> ")"

{-| Show a list of intervals
(a,b) | (c,d) | (e,f) | ... -}
showIntervals :: Show a => [Interval a] -> String
showIntervals = foldl' f ""
  where
    f [] x = showInterval x
    f acc x = acc <> " | " <> showInterval x

rangeToInterval :: forall a. Ord a => (a, a) -> RangeConstraint a -> Interval a
rangeToInterval (min', max') a =
  let value = rangeValue a
   in if min' > value || max' < value
        then error "rangeToInterval: value not in range"
        else toInterval a
  where
    toInterval :: RangeConstraint a -> Interval a
    toInterval (NL v) = (Closed min', Open v)
    toInterval (NG v) = (Open v, Closed max')
    toInterval (NLEQ v) = (Closed min', Closed v)
    toInterval (NGEQ v) = (Closed v, Closed max')
    toInterval (NEQ v) = (Closed v, Closed v)

negateRange :: RangeConstraint a -> [RangeConstraint a]
negateRange (NL a) = [NGEQ a]
negateRange (NG a) = [NLEQ a]
negateRange (NLEQ a) = [NG a]
negateRange (NGEQ a) = [NL a]
negateRange (NEQ a) = [NL a, NG a]

mergeIntervals :: (Num a, Ord a) => Interval a -> Interval a -> [Interval a]
-- if the b value is less than the c value, then the intervals
-- do not overlap
mergeIntervals (a, b) (c, d)
  | boundaryValue b < boundaryValue c = [(a, b), (c, d)]
-- if the b value is equal to the c value
-- but both are open, then the intervals do not overlap
mergeIntervals (a, Open b) (Open c, d)
  | b == c = [(a, Open b), (Open c, d)]
mergeIntervals (a, b) (c, d) = [(min a c, max b d)]

mergeIntervalList :: forall a. (Num a, Ord a) => [Interval a] -> [Interval a]
mergeIntervalList list = merge sorted
  where
    sorted = sortOn fst list

    merge :: [Interval a] -> [Interval a]
    merge [] = []
    merge [x] = [x]
    merge (x : y : xs) = case mergeIntervals x y of
      [] -> merge xs
      [x1] -> merge (x1 : xs)
      x1 : x2 : _ -> x1 : merge (x2 : xs)

reverseBoundary :: Boundary a -> Boundary a
reverseBoundary (Closed a) = Open a
reverseBoundary (Open a) = Closed a

type Domain a = Interval a

diff :: (Num a, Ord a) => Domain a -> Interval a -> (Maybe (Interval a), Maybe (Interval a))
diff (a, b) (c, d) = (first, second)
  where
    first = guard (a < c) >> Just (a, reverseBoundary c)
    second = guard (d < b) >> Just (reverseBoundary d, b)

intervalPoints :: Interval a -> [Boundary a]
intervalPoints (a, b) = [a, b]

intervalsToPoints :: [Interval a] -> [Boundary a]
intervalsToPoints = concatMap intervalPoints

addDomainPoints :: (Num a, Ord a) => Domain a -> [Boundary a] -> [Boundary a]
addDomainPoints d [] = intervalPoints d
addDomainPoints _ [_] = error "addDomainPoints: invalid input"
addDomainPoints (a, b) (head' : xs) =
  let
    lst = last xs
    middle = take (length xs - 1) xs
    begin = if a < head' then [a, reverseBoundary head'] else []
    end = if lst < b then [reverseBoundary lst, b] else []
   in
    begin ++ map reverseBoundary middle ++ end

boundaryListToIntervalList :: [Boundary a] -> [Interval a]
boundaryListToIntervalList [] = []
boundaryListToIntervalList (x : y : xs) = (x, y) : boundaryListToIntervalList xs
boundaryListToIntervalList [_] = error "boundaryListToIntervalList: invalid input"

gaps :: (Num a, Ord a) => Domain a -> [Interval a] -> [Interval a]
gaps d intervals =
  let merged = mergeIntervalList intervals
      points = addDomainPoints d $ intervalsToPoints merged
   in boundaryListToIntervalList points

gapsWithinRange :: (Num a, Ord a) => (a, a) -> [RangeConstraint a] -> [Interval a]
gapsWithinRange d@(d1, d2) ranges =
  let intervals = map (rangeToInterval d) ranges
      d' = (Closed d1, Closed d2)
   in gaps d' intervals

{-
>>> gapsWithinRange (0,10) [NL 1, NG 5]
[(Closed 1,Closed 5)]

>>> -- not less then , and not greater than 6 and not equal to 0
>>> gapsWithinRange (-10,10) [NL 1, NG 6, NEQ 0]
[(Closed 1,Closed 6)]

>>> -- not less then 3 , not greater than 6 and not less then 0
>>> gapsWithinRange (-10,10) [NL 3, NG 6, NL 0]
[(Closed 3,Closed 6)]

>>> -- not less then 1 and not greater than 5 and equal to 0
>>> gapsWithinRange (-10,10) $ [NL 1, NG 5 ] ++ negateRange (NEQ 0)
[]

>>> -- not less then 1 and not greater than 5 and equal to 3
>>> gapsWithinRange (-10,10) $ [NL 1, NG 5 ] ++ negateRange (NEQ 3)
[(Closed 3,Closed 3)]

>>> gapsWithinRange (-10,10) [NEQ 0]
[(Closed (-10),Open 0),(Open 0,Closed 10)]

>>> gapsWithinRange (0,10) [NL 1]
[(Closed 1,Closed 10)]

>>> gapsWithinRange (-5000,5000) $ negateRange (NL 30) ++ [NL 0, NG 1000]
[(Closed 0,Open 30)]

-}

--------------------------------------------------------------------------------
-- | Generators
generateFromInterval :: (HasRange a, Ord a) => Interval a -> Gen a
generateFromInterval (a, b) =
  let range = choose' (boundaryValue a, boundaryValue b)
   in case (a, b) of
        (Closed _, Closed _) -> range
        (Open _, Open _) -> range `suchThat` (\x -> x > boundaryValue a && x < boundaryValue b)
        (Closed _, Open _) -> range `suchThat` (\x -> x < boundaryValue b)
        (Open _, Closed _) -> range `suchThat` (\x -> x > boundaryValue a)

generateFromIntervals :: (HasRange a, Ord a) => [Interval a] -> Gen a
generateFromIntervals = oneof . map generateFromInterval

generateFromConstraints
  :: (HasRange a, Ord a, Num a)
  => (a, a)
  -> [RangeConstraint a]
  -> Gen a
generateFromConstraints d ranges = generateFromIntervals $ gapsWithinRange d ranges

rangeGen
  :: forall a
   . (Num a, HasDomain a, HasRange a, Ord a)
  => RangeConstraint a
  -> Gen a
rangeGen = rangeGen' domain

rangeGen'
  :: forall a
   . (Num a, HasRange a, Ord a)
  => (a, a)
  -> RangeConstraint a
  -> Gen a
rangeGen' (lower, upper) range = case range of
  NL x -> choose' (lower, x) `suchThat` (< x)
  NG x -> choose' (x, max upper (upper + x)) `suchThat` (> x)
  NEQ x -> pure x
  NLEQ x -> choose' (lower, x)
  NGEQ x -> choose' (x, upper)
