{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Text.Prettyprint.Doc.Extras(
    PrettyShow(..)
    , Pretty(..)
    , PrettyFoldable(..)
    , Tagged(Tagged)
    ) where

import           Data.Foldable             (Foldable (toList))
import           Data.Proxy                (Proxy (..))
import           Data.String               (IsString (..))
import           Data.Tagged
import           Data.Text.Prettyprint.Doc
import           GHC.TypeLits              (KnownSymbol, symbolVal)

-- | Newtype wrapper for deriving 'Pretty' via a 'Show' instance
newtype PrettyShow a = PrettyShow { unPrettyShow :: a }

instance Show a => Pretty (PrettyShow a) where
  pretty = viaShow . unPrettyShow

-- | Newtype wrapper for deriving 'Pretty' for a 'Foldable' container by
--   calling 'toList'.
newtype PrettyFoldable f a = PrettyFoldable { unPrettyFoldable :: f a }

instance (Foldable f, Pretty a) => Pretty (PrettyFoldable f a) where
  pretty = pretty . toList . unPrettyFoldable

instance (KnownSymbol a, Pretty b) => Pretty (Tagged a b) where
  pretty = prettyTagged

prettyTagged :: forall a b ann. (KnownSymbol a, Pretty b) => Tagged a b -> Doc ann
prettyTagged (Tagged b) = fromString (symbolVal (Proxy @a)) <+> pretty b
