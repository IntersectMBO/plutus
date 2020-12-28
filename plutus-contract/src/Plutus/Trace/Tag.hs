{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Plutus.Trace.Tag(Tag(..)) where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.String               (IsString (..))
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc (Pretty (..), braces)
import           GHC.Generics              (Generic)

-- | A human-readably piece of data, used to identify threads and contract
--   instances. See note [Thread Tag]
newtype Tag = Tag { unTag :: Text }
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (ToJSON, FromJSON, IsString)

instance Pretty Tag where
    pretty = braces . pretty . unTag
