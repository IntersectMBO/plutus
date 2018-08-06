module PlutusPrelude ( -- * Reëxports from base
                       (&&&)
                     , toList
                     , bool
                     , first
                     , second
                     , on
                     , fold
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , Word8
                     , Semigroup (..)
                     -- * Reëxports from "Control.Composition"
                     , (.*)
                     -- * Custom functions
                     , prettyText
                     , render
                     , repeatM
                     , Debug (..)
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

-- | This is like 'Pretty', but it dumps 'Unique's for each 'Name' / 'TyName' as
-- well.
class Debug a where
    debug :: a -> Doc ann

-- | Render a 'Program' as strict 'Text'.
prettyText :: Pretty a => a -> T.Text
prettyText = render . pretty

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions

-- | Make sure your 'Applicative' is sufficiently lazy!
repeatM :: Applicative f => f a -> f [a]
repeatM x = (:) <$> x <*> repeatM x
