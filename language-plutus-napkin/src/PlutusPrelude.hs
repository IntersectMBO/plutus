module PlutusPrelude ( (<=<)
                     , (&&&)
                     , toList
                     , bool
                     , first
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     ) where

import           Control.Arrow      (first, (&&&))
import           Control.DeepSeq    (NFData)
import           Control.Monad      ((<=<))
import           Data.Bool          (bool)
import           Data.Foldable      (toList)
import           Data.List.NonEmpty (NonEmpty (..))
import           GHC.Generics       (Generic)
import           GHC.Natural        (Natural)
