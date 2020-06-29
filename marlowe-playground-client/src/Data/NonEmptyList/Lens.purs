module Data.NonEmptyList.Lens where

import Data.Lens (Lens', lens)
import Data.List.NonEmpty (cons', head, tail, uncons)
import Data.List.Types (List, NonEmptyList)

_Head :: forall a. Lens' (NonEmptyList a) a
_Head = lens head (\l new -> let { head, tail } = uncons l in cons' new tail)

_Tail :: forall a. Lens' (NonEmptyList a) (List a)
_Tail = lens get set
  where
  get = tail

  set nel list = cons' (head nel) list
