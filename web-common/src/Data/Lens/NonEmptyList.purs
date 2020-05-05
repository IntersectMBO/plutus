module Data.Lens.NonEmptyList where

import Data.Lens (Lens, lens)
import Data.List.NonEmpty (head, uncons, cons')
import Data.List.Types (NonEmptyList)

_Head :: forall a. Lens (NonEmptyList a) (NonEmptyList a) a a
_Head = lens head (\l new -> let { head, tail } = uncons l in cons' new tail)
