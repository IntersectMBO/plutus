{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusTx.Blueprint.Preamble where

import Prelude

import Data.Aeson (Options (..), defaultOptions)
import Data.Aeson.Extra (stripPrefix)
import Data.Aeson.TH (deriveToJSON)
import Data.Text (Text)
import GHC.Generics (Generic)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion)

-- | Meta-information about the contract
data Preamble = MkPreamble
  { preambleTitle :: Text
  -- ^ A short and descriptive title of the contract application
  , preambleDescription :: Maybe Text
  -- ^ A more elaborate description
  , preambleVersion :: Text
  -- ^ A version number for the project.
  , preamblePlutusVersion :: PlutusVersion
  -- ^ The Plutus version assumed for all validators
  , preambleLicense :: Maybe Text
  {-^ A license under which the specification
  and contract code is distributed -}
  }
  deriving stock (Show, Generic)

$(deriveToJSON defaultOptions {fieldLabelModifier = stripPrefix "preamble"} ''Preamble)
