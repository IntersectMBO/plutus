-- Fake a builder
module Data.Text.Lazy.Builder
   ( Builder
   , LazyTextBuilder
   , toLazyText
   , toLazyTextWith
   , singleton
   , fromText
   , fromLazyText
   , fromString
   , flush
   ) where
import Data.String
import Data.Text qualified as S
import Data.Text.Lazy qualified as L

newtype Builder = B L.Text
  deriving newtype (Eq, Ord, {-Semigroup,-} Monoid, Show, IsString)

-- bug in newtype deriving
instance Semigroup Builder where
  B x <> B y = B (x <> y)

type LazyTextBuilder = Builder

toLazyText :: Builder -> L.Text
toLazyText (B t) = t

toLazyTextWith :: Int -> Builder -> L.Text
toLazyTextWith _ (B t) = t

singleton :: Char -> Builder
singleton c = B (L.singleton c)

fromText :: S.Text -> Builder
fromText = fromLazyText . L.toLazy

fromLazyText :: L.Text -> Builder
fromLazyText t = B t

flush :: Builder
flush = B L.empty
