-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Result
    ( EvaluationResult(..)
    , evaluationResultToMaybe
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | The type of results various evaluation engines return.
data EvaluationResult
    = EvaluationSuccess (Value TyName Name ())
    | EvaluationFailure
    deriving (Show, Eq)

instance PrettyBy config (Value TyName Name ()) => PrettyBy config EvaluationResult where
    prettyBy config (EvaluationSuccess value) = prettyBy config value
    prettyBy _      EvaluationFailure         = "Failure"

-- | Map 'EvaluationSuccess' to 'Just' and 'EvaluationFailure' to 'Nothing'.
evaluationResultToMaybe :: EvaluationResult -> Maybe (Value TyName Name ())
evaluationResultToMaybe (EvaluationSuccess res) = Just res
evaluationResultToMaybe EvaluationFailure       = Nothing
