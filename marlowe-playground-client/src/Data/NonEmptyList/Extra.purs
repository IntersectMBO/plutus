module Data.NonEmptyList.Extra where

import Prologue
import Data.List.NonEmpty (cons, fromList, head, tail)
import Data.List.Types (NonEmptyList)

-- | Apply a function to the head of a non-empty list and attach the result to the front
-- | of the list
extendWith :: forall a. (a -> a) -> NonEmptyList a -> NonEmptyList a
extendWith f l = cons ((f <<< head) l) l

tailIfNotEmpty :: forall a. NonEmptyList a -> NonEmptyList a
tailIfNotEmpty ms = case fromList (tail ms) of
  Nothing -> ms
  Just netail -> netail
