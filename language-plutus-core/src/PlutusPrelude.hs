module PlutusPrelude ( (&&&)
                     , toList
                     , bool
                     , first
                     , second
                     , on
                     , fold
                     , (.*)
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , Word8
                     , Semigroup (..)
                     , module X
                     ) where

import           Control.Arrow             ((&&&))
import           Control.Composition       ((.*))
import           Control.DeepSeq           (NFData)
import           Data.Bifunctor            (first, second)
import           Data.Bool                 (bool)
import           Data.Foldable             (fold, toList)
import           Data.Function             (on)
import           Data.List.NonEmpty        (NonEmpty (..))
import           Data.Semigroup
import           Data.Text.Prettyprint.Doc
import           Data.Word                 (Word8)
import           Debug.Trace               as X
import           GHC.Generics              (Generic)
import           GHC.Natural               (Natural)
