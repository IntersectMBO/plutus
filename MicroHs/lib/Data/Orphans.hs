-- Instance declarations that can't be put where
-- due to import cycles.
module Data.Orphans where
import qualified Prelude(); import MiniPrelude

instance (Show a) => Show (Down a) where
  showsPrec d (Down x) = showParen (d > 10) $
    showString "Down " . showsPrec 11 x
