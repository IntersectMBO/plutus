module PlutusCore.InlineUtils (InlineHints (..), ShouldInline) where

import Data.Semigroup (Any (..))

type ShouldInline name a =
    -- | Binder annotation
    a ->
    -- | Binder name
    name ->
    -- | RHS annotation
    a ->
    Bool

newtype InlineHints name a = InlineHints {shouldInline :: ShouldInline name a}
    deriving (Semigroup, Monoid) via (a -> name -> a -> Any)

instance Show (InlineHints name a) where
    show _ = "<inline hints>"
