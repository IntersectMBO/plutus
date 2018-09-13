-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Evaluation.Result
    ( EvaluationResult(..)
    , evaluationResultToMaybe
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Type

-- | The type of results various evaluation engines return.
data EvaluationResult
    = EvaluationSuccess (Value TyName Name ())
    | EvaluationFailure
    deriving (Show, Eq)

instance PrettyCfg EvaluationResult where
    prettyCfg cfg (EvaluationSuccess value) = prettyCfg cfg value
    prettyCfg _   EvaluationFailure         = "Failure"

-- | Map 'EvaluationSuccess' to 'Just' and 'EvaluationFailure' to 'Nothing'.
evaluationResultToMaybe :: EvaluationResult -> Maybe (Value TyName Name ())
evaluationResultToMaybe (EvaluationSuccess res) = Just res
evaluationResultToMaybe EvaluationFailure       = Nothing
