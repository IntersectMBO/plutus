-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Result
    ( EvaluationResultF (EvaluationSuccess, EvaluationFailure)
    , EvaluationResult
    , evaluationResultToMaybe
    , maybeToEvaluationResult
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type

-- | The parameterized type of results various evaluation engines return.
data EvaluationResultF a
    = EvaluationSuccess a
    | EvaluationFailure
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative EvaluationResultF where
    pure = EvaluationSuccess

    EvaluationSuccess f <*> a = fmap f a
    EvaluationFailure   <*> _ = EvaluationFailure

instance Monad EvaluationResultF where
    EvaluationSuccess x >>= f = f x
    EvaluationFailure   >>= _ = EvaluationFailure

-- | The type of results various evaluation engines return.
type EvaluationResult = EvaluationResultF (Value TyName Name ())

instance PrettyBy config (Value TyName Name ()) => PrettyBy config EvaluationResult where
    prettyBy config (EvaluationSuccess value) = prettyBy config value
    prettyBy _      EvaluationFailure         = "Failure"

instance Pretty EvaluationResult where
    pretty = prettyPlcDef

-- | Map 'EvaluationSuccess' to 'Just' and 'EvaluationFailure' to 'Nothing'.
evaluationResultToMaybe :: EvaluationResult -> Maybe (Value TyName Name ())
evaluationResultToMaybe (EvaluationSuccess res) = Just res
evaluationResultToMaybe EvaluationFailure       = Nothing

-- | Map 'Just' to 'EvaluationSuccess' and 'Nothing' to 'EvaluationFailure'.
maybeToEvaluationResult :: Maybe (Value TyName Name ()) -> EvaluationResult
maybeToEvaluationResult (Just res) = EvaluationSuccess res
maybeToEvaluationResult Nothing    = EvaluationFailure
