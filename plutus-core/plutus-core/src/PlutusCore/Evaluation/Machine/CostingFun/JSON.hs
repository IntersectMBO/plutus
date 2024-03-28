{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O0               #-}

-- | A separate module for JSON instances, so that we can stick @-O0@ on it and avoid spending
-- a lot of time optimizing loads of Core whose performance doesn't matter.
module PlutusCore.Evaluation.Machine.CostingFun.JSON () where

import Data.Aeson
import Deriving.Aeson

import PlutusCore.Evaluation.Machine.CostingFun.Core

type ModelJSON prefix = CustomJSON '[FieldLabelModifier (StripPrefix prefix, CamelToSnake)]

type ModelArgumentJSON prefix =
    CustomJSON
        -- Without TagSingleConstructors the format can change unexpectedly if
        -- you add/remove constructors because you don't get the tags if there's
        -- only one constructor but you do if there's more than one.
        '[ TagSingleConstructors
         , SumTaggedObject "type" "arguments"
         , ConstructorTagModifier (StripPrefix prefix, CamelToSnake)]

deriving via ModelJSON "costingFun" (CostingFun model)
    instance FromJSON model => FromJSON (CostingFun model)
deriving via ModelJSON "costingFun" (CostingFun model)
    instance ToJSON model => ToJSON (CostingFun model)

deriving newtype instance FromJSON Intercept
deriving newtype instance ToJSON   Intercept
deriving newtype instance FromJSON Slope
deriving newtype instance ToJSON   Slope
deriving newtype instance FromJSON Coefficient0
deriving newtype instance ToJSON   Coefficient0
deriving newtype instance FromJSON Coefficient1
deriving newtype instance ToJSON   Coefficient1
deriving newtype instance FromJSON Coefficient2
deriving newtype instance ToJSON   Coefficient2

deriving via ModelArgumentJSON "ModelOneArgument" ModelOneArgument
    instance FromJSON ModelOneArgument
deriving via ModelArgumentJSON "ModelOneArgument" ModelOneArgument
    instance ToJSON ModelOneArgument
deriving via ModelArgumentJSON "ModelTwoArguments" ModelTwoArguments
    instance FromJSON ModelTwoArguments
deriving via ModelArgumentJSON "ModelTwoArguments" ModelTwoArguments
    instance ToJSON ModelTwoArguments
deriving via ModelArgumentJSON "ModelThreeArguments" ModelThreeArguments
    instance FromJSON ModelThreeArguments
deriving via ModelArgumentJSON "ModelThreeArguments" ModelThreeArguments
    instance ToJSON ModelThreeArguments
deriving via ModelArgumentJSON "ModelFourArguments" ModelFourArguments
    instance FromJSON ModelFourArguments
deriving via ModelArgumentJSON "ModelFourArguments" ModelFourArguments
    instance ToJSON ModelFourArguments
deriving via ModelArgumentJSON "ModelFiveArguments" ModelFiveArguments
    instance FromJSON ModelFiveArguments
deriving via ModelArgumentJSON "ModelFiveArguments" ModelFiveArguments
    instance ToJSON ModelFiveArguments
deriving via ModelArgumentJSON "ModelSixArguments" ModelSixArguments
    instance FromJSON ModelSixArguments
deriving via ModelArgumentJSON "ModelSixArguments" ModelSixArguments
    instance ToJSON ModelSixArguments

deriving via ModelJSON "modelSubtractedSizes" ModelSubtractedSizes
    instance FromJSON ModelSubtractedSizes
deriving via ModelJSON "modelSubtractedSizes" ModelSubtractedSizes
    instance ToJSON ModelSubtractedSizes
deriving via ModelJSON "oneVariableLinearFunction" OneVariableLinearFunction
    instance FromJSON OneVariableLinearFunction
deriving via ModelJSON "oneVariableLinearFunction" OneVariableLinearFunction
    instance ToJSON OneVariableLinearFunction
deriving via ModelJSON "twoVariableLinearFunction" TwoVariableLinearFunction
    instance FromJSON TwoVariableLinearFunction
deriving via ModelJSON "twoVariableLinearFunction" TwoVariableLinearFunction
    instance ToJSON TwoVariableLinearFunction
deriving via ModelJSON "oneVariableQuadraticFunction" OneVariableQuadraticFunction
    instance FromJSON OneVariableQuadraticFunction
deriving via ModelJSON "oneVariableQuadraticFunction" OneVariableQuadraticFunction
    instance ToJSON OneVariableQuadraticFunction
deriving via ModelJSON "modelConstantOrOneArgument" ModelConstantOrOneArgument
    instance FromJSON ModelConstantOrOneArgument
deriving via ModelJSON "modelConstantOrOneArgument" ModelConstantOrOneArgument
    instance ToJSON ModelConstantOrOneArgument
deriving via ModelJSON "modelConstantOrTwoArguments" ModelConstantOrTwoArguments
    instance FromJSON ModelConstantOrTwoArguments
deriving via ModelJSON "modelConstantOrTwoArguments" ModelConstantOrTwoArguments
    instance ToJSON ModelConstantOrTwoArguments
