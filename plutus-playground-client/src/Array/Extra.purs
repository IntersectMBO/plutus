module Array.Extra where

import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Tuple.Nested (type (/\), (/\))

--| Turn a nested foldable into an array with keys. So, for example, a
-- `List (Map String Bool)` would become an `Array (Int /\ String /\ Bool)`.
collapse ::
  forall m n i j a.
  FoldableWithIndex i m =>
  FoldableWithIndex j n =>
  m (n a) ->
  Array (i /\ j /\ a)
collapse = foldMapWithIndex (\i -> foldMapWithIndex (\j a -> [ i /\ j /\ a ]))
