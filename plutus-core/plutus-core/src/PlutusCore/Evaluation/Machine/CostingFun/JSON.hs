{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| A separate module for JSON instances, so that we can stick @-O0@ on it and avoid spending
a lot of time optimizing loads of Core whose performance doesn't matter. -}
module PlutusCore.Evaluation.Machine.CostingFun.JSON () where

import Data.Aeson
import Data.List (stripPrefix)
import Data.Maybe (fromMaybe)

import PlutusCore.Evaluation.Machine.CostingFun.Core

-- | Drop a prefix from a name, leaving the name unchanged if the prefix doesn't match.
dropPrefix :: String -> String -> String
dropPrefix prefix s = fromMaybe s (stripPrefix prefix s)

{-| JSON options for the record types describing the shapes of costing functions: drop the
type-name prefix from the field names and convert the rest to snake_case. -}
modelOptions :: String -> Options
modelOptions prefix =
  defaultOptions {fieldLabelModifier = camelTo2 '_' . dropPrefix prefix}

{-| JSON options for the sum types of costing function shapes.
Without 'tagSingleConstructors' the format can change unexpectedly if
you add/remove constructors because you don't get the tags if there's
only one constructor but you do if there's more than one. -}
modelArgumentOptions :: String -> Options
modelArgumentOptions prefix =
  defaultOptions
    { constructorTagModifier = camelTo2 '_' . dropPrefix prefix
    , sumEncoding = TaggedObject "type" "arguments"
    , tagSingleConstructors = True
    }

instance FromJSON model => FromJSON (CostingFun model) where
  parseJSON = genericParseJSON (modelOptions "costingFun")

instance ToJSON model => ToJSON (CostingFun model) where
  toJSON = genericToJSON (modelOptions "costingFun")
  toEncoding = genericToEncoding (modelOptions "costingFun")

deriving newtype instance FromJSON Intercept
deriving newtype instance ToJSON Intercept
deriving newtype instance FromJSON Slope
deriving newtype instance ToJSON Slope
deriving newtype instance FromJSON Coefficient0
deriving newtype instance ToJSON Coefficient0
deriving newtype instance FromJSON Coefficient1
deriving newtype instance ToJSON Coefficient1
deriving newtype instance FromJSON Coefficient2
deriving newtype instance ToJSON Coefficient2
deriving newtype instance FromJSON Coefficient00
deriving newtype instance ToJSON Coefficient00
deriving newtype instance FromJSON Coefficient10
deriving newtype instance ToJSON Coefficient10
deriving newtype instance FromJSON Coefficient01
deriving newtype instance ToJSON Coefficient01
deriving newtype instance FromJSON Coefficient20
deriving newtype instance ToJSON Coefficient20
deriving newtype instance FromJSON Coefficient11
deriving newtype instance ToJSON Coefficient11
deriving newtype instance FromJSON Coefficient02
deriving newtype instance ToJSON Coefficient02
deriving newtype instance FromJSON Coefficient12
deriving newtype instance ToJSON Coefficient12

instance FromJSON ModelOneArgument where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelOneArgument")

instance ToJSON ModelOneArgument where
  toJSON = genericToJSON (modelArgumentOptions "ModelOneArgument")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelOneArgument")

instance FromJSON ModelTwoArguments where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelTwoArguments")

instance ToJSON ModelTwoArguments where
  toJSON = genericToJSON (modelArgumentOptions "ModelTwoArguments")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelTwoArguments")

instance FromJSON ModelThreeArguments where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelThreeArguments")

instance ToJSON ModelThreeArguments where
  toJSON = genericToJSON (modelArgumentOptions "ModelThreeArguments")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelThreeArguments")

instance FromJSON ModelFourArguments where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelFourArguments")

instance ToJSON ModelFourArguments where
  toJSON = genericToJSON (modelArgumentOptions "ModelFourArguments")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelFourArguments")

instance FromJSON ModelFiveArguments where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelFiveArguments")

instance ToJSON ModelFiveArguments where
  toJSON = genericToJSON (modelArgumentOptions "ModelFiveArguments")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelFiveArguments")

instance FromJSON ModelSixArguments where
  parseJSON = genericParseJSON (modelArgumentOptions "ModelSixArguments")

instance ToJSON ModelSixArguments where
  toJSON = genericToJSON (modelArgumentOptions "ModelSixArguments")
  toEncoding = genericToEncoding (modelArgumentOptions "ModelSixArguments")

instance FromJSON ModelSubtractedSizes where
  parseJSON = genericParseJSON (modelOptions "modelSubtractedSizes")

instance ToJSON ModelSubtractedSizes where
  toJSON = genericToJSON (modelOptions "modelSubtractedSizes")
  toEncoding = genericToEncoding (modelOptions "modelSubtractedSizes")

instance FromJSON OneVariableLinearFunction where
  parseJSON = genericParseJSON (modelOptions "oneVariableLinearFunction")

instance ToJSON OneVariableLinearFunction where
  toJSON = genericToJSON (modelOptions "oneVariableLinearFunction")
  toEncoding = genericToEncoding (modelOptions "oneVariableLinearFunction")

instance FromJSON TwoVariableLinearFunction where
  parseJSON = genericParseJSON (modelOptions "twoVariableLinearFunction")

instance ToJSON TwoVariableLinearFunction where
  toJSON = genericToJSON (modelOptions "twoVariableLinearFunction")
  toEncoding = genericToEncoding (modelOptions "twoVariableLinearFunction")

instance FromJSON OneVariableQuadraticFunction where
  parseJSON = genericParseJSON (modelOptions "oneVariableQuadraticFunction")

instance ToJSON OneVariableQuadraticFunction where
  toJSON = genericToJSON (modelOptions "oneVariableQuadraticFunction")
  toEncoding = genericToEncoding (modelOptions "oneVariableQuadraticFunction")

instance FromJSON TwoVariableQuadraticFunction where
  parseJSON = genericParseJSON (modelOptions "twoVariableQuadraticFunction")

instance ToJSON TwoVariableQuadraticFunction where
  toJSON = genericToJSON (modelOptions "twoVariableQuadraticFunction")
  toEncoding = genericToEncoding (modelOptions "twoVariableQuadraticFunction")

instance FromJSON ExpModCostingFunction where
  parseJSON = genericParseJSON (modelOptions "expModCostingFunction")

instance ToJSON ExpModCostingFunction where
  toJSON = genericToJSON (modelOptions "expModCostingFunction")
  toEncoding = genericToEncoding (modelOptions "expModCostingFunction")

instance FromJSON ModelConstantOrOneArgument where
  parseJSON = genericParseJSON (modelOptions "modelConstantOrOneArgument")

instance ToJSON ModelConstantOrOneArgument where
  toJSON = genericToJSON (modelOptions "modelConstantOrOneArgument")
  toEncoding = genericToEncoding (modelOptions "modelConstantOrOneArgument")

instance FromJSON ModelConstantOrTwoArguments where
  parseJSON = genericParseJSON (modelOptions "modelConstantOrTwoArguments")

instance ToJSON ModelConstantOrTwoArguments where
  toJSON = genericToJSON (modelOptions "modelConstantOrTwoArguments")
  toEncoding = genericToEncoding (modelOptions "modelConstantOrTwoArguments")

-- See Note [Backward compatibility for costing functions] for ModelConstantOrLinear
instance FromJSON ModelConstantOrLinear where
  parseJSON = genericParseJSON (modelOptions "modelConstantOrLinear")

instance ToJSON ModelConstantOrLinear where
  toJSON = genericToJSON (modelOptions "modelConstantOrLinear")
  toEncoding = genericToEncoding (modelOptions "modelConstantOrLinear")

instance FromJSON TwoVariableWithInteractionFunction where
  parseJSON = genericParseJSON (modelOptions "twoVariableWithInteractionFunction")

instance ToJSON TwoVariableWithInteractionFunction where
  toJSON = genericToJSON (modelOptions "twoVariableWithInteractionFunction")
  toEncoding = genericToEncoding (modelOptions "twoVariableWithInteractionFunction")
