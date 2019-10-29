{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
module Data.Text.Prettyprint.Doc.Extras(
    PrettyShow(..)
    , PrettyFoldable(..)
    ) where

import           Data.Foldable             (Foldable (toList))
import           Data.Text.Prettyprint.Doc

-- | Newtype wrapper for deriving 'Pretty' via a 'Show' instance
newtype PrettyShow a = PrettyShow { unPrettyShow :: a }

instance Show a => Pretty (PrettyShow a) where
  pretty = viaShow . unPrettyShow

-- | Newtype wrapper for deriving 'Pretty' for a 'Foldable' container by
--   calling 'toList'.
newtype PrettyFoldable f a = PrettyFoldable { unPrettyFoldable :: f a }

instance (Foldable f, Pretty a) => Pretty (PrettyFoldable f a) where
  pretty = pretty . toList . unPrettyFoldable
