{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
module Data.Text.Prettyprint.Doc.Extras(
    PrettyShow(..)
    ) where

import           Data.Text.Prettyprint.Doc

-- | Newtype wrapper for deriving 'Pretty' via a 'Show' instance
newtype PrettyShow a = PrettyShow { unPrettyShow :: a }

instance Show a => Pretty (PrettyShow a) where
  pretty = viaShow . unPrettyShow
