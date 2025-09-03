-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Evaluation.Result
    ( EvaluationResult (..)
    , isEvaluationSuccess
    , isEvaluationFailure
    ) where

import PlutusPrelude

import PlutusCore.Pretty

import Control.Monad.Except (MonadError, catchError, throwError)

-- | The parameterized type of results various evaluation engines return.
data EvaluationResult a
    = EvaluationSuccess !a
    | EvaluationFailure
    deriving stock (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (NFData)

instance MonadError () EvaluationResult where
    throwError () = EvaluationFailure
    {-# INLINE throwError #-}

    catchError EvaluationFailure f = f ()
    catchError x                 _ = x
    {-# INLINE catchError #-}

instance Applicative EvaluationResult where
    pure = EvaluationSuccess
    {-# INLINE pure #-}

    EvaluationSuccess f <*> a = fmap f a
    EvaluationFailure   <*> _ = EvaluationFailure
    {-# INLINE (<*>) #-}

    EvaluationSuccess _ *> b = b
    EvaluationFailure   *> _ = EvaluationFailure
    {-# INLINE (*>) #-}

instance Monad EvaluationResult where
    EvaluationSuccess x >>= f = f x
    EvaluationFailure   >>= _ = EvaluationFailure
    {-# INLINE (>>=) #-}

    (>>) = (*>)
    {-# INLINE (>>) #-}

instance Alternative EvaluationResult where
    empty = EvaluationFailure
    {-# INLINE empty #-}

    a@EvaluationSuccess{} <|> _ = a
    EvaluationFailure     <|> b = b
    {-# INLINE (<|>) #-}

instance MonadFail EvaluationResult where
    fail _ = EvaluationFailure
    {-# INLINE fail #-}

instance PrettyBy config a => PrettyBy config (EvaluationResult a) where
    prettyBy config (EvaluationSuccess x) = prettyBy config x
    prettyBy _      EvaluationFailure     = "Failure"

instance PrettyClassic a => Pretty (EvaluationResult a) where
    pretty = prettyClassic

-- | Check whether an 'EvaluationResult' is an 'EvaluationSuccess'.
isEvaluationSuccess :: EvaluationResult a -> Bool
isEvaluationSuccess = not . null

-- | Check whether an 'EvaluationResult' is an 'EvaluationFailure'.
isEvaluationFailure :: EvaluationResult a -> Bool
isEvaluationFailure = null
