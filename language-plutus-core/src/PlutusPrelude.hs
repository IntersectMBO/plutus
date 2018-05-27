module PlutusPrelude ( (&&&)
                     , toList
                     , bool
                     , first
                     , on
                     , fold
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , Word8
                     , (<>)
                     ) where

import           Control.Arrow             (first, (&&&))
import           Control.DeepSeq           (NFData)
import           Data.Bool                 (bool)
import           Data.Foldable             (fold, toList)
import           Data.Function             (on)
import           Data.List.NonEmpty        (NonEmpty (..))
import           Data.Semigroup
import           Data.Text.Prettyprint.Doc
import           Data.Word                 (Word8)
import           GHC.Generics              (Generic)
import           GHC.Natural               (Natural)
