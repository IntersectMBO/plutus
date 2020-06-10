module Data.Foldable.Extra
  ( interleave
  , countConsecutive
  ) where

import Data.Tuple.Nested
import Control.Applicative (class Applicative, pure)
import Data.Array as Array
import Data.Boolean (otherwise)
import Data.Eq (class Eq, (==))
import Data.Foldable (class Foldable, foldl, intercalate)
import Data.Function ((>>>))
import Data.Functor (map)
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.Semiring ((+))

interleave :: forall m a. Applicative m => Foldable m => Monoid (m a) => a -> m a -> m a
interleave sep xs = intercalate (pure sep) (map pure xs)

-- | Collapse a sequence of things that tend to repeat so that you
-- just get the thing, and how many times it appeared in a row. For
-- example, if you had a log of 100 ping messages followed by
-- something interesting, you'd get an array of
-- `[100 /\ Ping, 1 /\ InterestingThing]`.
countConsecutive :: forall f a. Eq a => Foldable f => f a -> Array (Int /\ a)
countConsecutive = tallyAll >>> finalize
  where
  tallyAll :: f a -> Tally a
  tallyAll =
    foldl tallyNext
      { count: 0
      , current: Nothing
      , result: mempty
      }

  tallyNext :: Tally a -> a -> Tally a
  tallyNext a@{ count, current: Just x, result } y
    | x == y =
      { count: count + 1
      , current: Just y
      , result
      }
    | otherwise =
      { count: 1
      , current: Just y
      , result: Array.snoc result (count /\ x)
      }

  tallyNext a@{ count, current: Nothing, result } y =
    { count: 1
    , current: Just y
    , result
    }

  finalize :: Tally a -> Array (Int /\ a)
  finalize { count, current: Just x, result } = Array.snoc result (count /\ x)

  finalize { result } = result

type Tally a
  = { current :: Maybe a
    , count :: Int
    , result :: Array (Int /\ a)
    }
