module PlutusCore.InlineUtils (InlineHints(..)) where

import Data.Semigroup (Any (..))

newtype InlineHints name a = InlineHints { shouldInline :: a -> name -> Bool }
    deriving (Semigroup, Monoid) via (a -> name -> Any)

instance Show (InlineHints name a) where
    show _ = "<inline hints>"
