-- | A custom prelude that re-exports the most commonly implorted modules.
module Prologue
  ( module Prelude
  , module Data.Either
  , module Data.Maybe
  , module Data.Tuple
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
