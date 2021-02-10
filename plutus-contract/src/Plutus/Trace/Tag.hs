{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Plutus.Trace.Tag(Tag(..)) where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.String               (IsString (..))
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc (Pretty (..), braces)
import           GHC.Generics              (Generic)

-- | A human-readable piece of data, used to identify threads and contract
--   instances. See note [Thread Tag]
newtype Tag = Tag { unTag :: Text }
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (IsString)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty Tag where
    pretty = braces . pretty . unTag
