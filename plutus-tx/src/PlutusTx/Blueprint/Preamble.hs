{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusTx.Blueprint.Preamble where

import Prelude

import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.Maybe (catMaybes)
import Data.Text (Text)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion)

-- | Meta-information about the contract
data Preamble = MkPreamble
  { preambleTitle         :: Text
  -- ^ A short and descriptive title of the contract application
  , preambleDescription   :: Maybe Text
  -- ^ A more elaborate description
  , preambleVersion       :: Text
  -- ^ A version number for the project.
  , preamblePlutusVersion :: PlutusVersion
  -- ^ The Plutus version assumed for all validators
  , preambleLicense       :: Maybe Text
  -- ^ A license under which the specification
  -- and contract code is distributed
  }
  deriving stock (Show)

instance ToJSON Preamble where
  toJSON MkPreamble{..} =
    Aeson.object
      $ catMaybes
        [ Just $ "title" .= preambleTitle
        , fmap ("description" .=) preambleDescription
        , Just $ "version" .= preambleVersion
        , Just $ "plutusVersion" .= preamblePlutusVersion
        , fmap ("license" .=) preambleLicense
        ]
