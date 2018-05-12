module PlutusPrelude ( (&&&)
                     , toList
                     , bool
                     , first
                     , on
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , (<>)
                     ) where

import           Control.Arrow             (first, (&&&))
import           Control.DeepSeq           (NFData)
import           Data.Bool                 (bool)
import           Data.Foldable             (toList)
import           Data.Function             (on)
import           Data.List.NonEmpty        (NonEmpty (..))
import           Data.Semigroup
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           GHC.Natural               (Natural)
