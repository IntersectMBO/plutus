module PlutusPrelude ( (&&&)
                     , toList
                     , bool
                     , first
                     , second
                     , on
                     , fold
                     , (.*)
                     -- * Custom functions
                     , prettyText
                     , render
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , Word8
                     , Semigroup (..)
                     -- Reëxports from "Data.Text.Prettyprint.Doc"
                     , (<+>)
                     , parens
                     , squotes
                     , Doc
                     ) where

import           Control.Arrow                         ((&&&))
import           Control.Composition                   ((.*))
import           Control.DeepSeq                       (NFData)
import           Data.Bifunctor                        (first, second)
import           Data.Bool                             (bool)
import           Data.Foldable                         (fold, toList)
import           Data.Function                         (on)
import           Data.List.NonEmpty                    (NonEmpty (..))
import           Data.Semigroup
import qualified Data.Text                             as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Data.Word                             (Word8)
import           GHC.Generics                          (Generic)
import           GHC.Natural                           (Natural)

-- | Render a 'Program' as strict 'Text'.
prettyText :: Pretty a => a -> T.Text
prettyText = render . pretty

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions
