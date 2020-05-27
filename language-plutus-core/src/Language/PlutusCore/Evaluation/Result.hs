-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Result
    ( EvaluationResult (..)
    , EvaluationResultDef
    , isEvaluationSuccess
    , isEvaluationFailure
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty

import           Control.Applicative
import           PlutusPrelude

-- | The parameterized type of results various evaluation engines return.
-- On the PLC side this becomes (via @makeKnown@) either a call to 'error' or
-- a value of the PLC counterpart of type @a@.
data EvaluationResult a
    = EvaluationSuccess a
    | EvaluationFailure
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable, NFData)

-- | The default exception-free type of results various evaluation engines return.
type EvaluationResultDef uni = EvaluationResult (Term TyName Name uni ())

instance Applicative EvaluationResult where
    pure = EvaluationSuccess

    EvaluationSuccess f <*> a = fmap f a
    EvaluationFailure   <*> _ = EvaluationFailure

instance Monad EvaluationResult where
    EvaluationSuccess x >>= f = f x
    EvaluationFailure   >>= _ = EvaluationFailure

instance Alternative EvaluationResult where
    empty = EvaluationFailure

    EvaluationSuccess x <|> _ = EvaluationSuccess x
    EvaluationFailure   <|> a = a

instance PrettyBy config a => PrettyBy config (EvaluationResult a) where
    prettyBy config (EvaluationSuccess value) = prettyBy config value
    prettyBy _      EvaluationFailure         = "Failure"

instance PrettyClassic a => Pretty (EvaluationResult a) where
    pretty = prettyClassicDef

-- | Check whether an 'EvaluationResult' is an 'EvaluationSuccess'.
isEvaluationSuccess :: EvaluationResult a -> Bool
isEvaluationSuccess = not . null

-- | Check whether an 'EvaluationResult' is an 'EvaluationFailure'.
isEvaluationFailure :: EvaluationResult a -> Bool
isEvaluationFailure = null
