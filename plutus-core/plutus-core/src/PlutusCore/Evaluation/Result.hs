-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Evaluation.Result
    ( AsEvaluationFailure (..)
    , evaluationFailure
    , _EvaluationFailureVia
    , EvaluationResult (..)
    , isEvaluationSuccess
    , isEvaluationFailure
    ) where

import           PlutusPrelude

import           PlutusCore.Pretty

import           Control.Lens
import           Control.Monad.Except

-- Note that we can't just use 'makeClassyPrisms' for 'EvaluationResult' as that would generate
-- @_EvaluationSuccess@ as well as @_EvaluationFailure@, which would no longer be prismatic error
-- handling: it'd constrain the monad, not the error in it.
--
-- We could define
--
--     data EvaluationFailure = EvaluationFailure
--
-- just for the purpose of using 'makeClassyPrisms' over it, but then it's clearer to write out
-- the class definition manually than to hide it behind a TH function called over a redundant
-- data type name-clashing with the useful 'EvaluationResult'.
-- | A class for viewing errors as evaluation failures (in the sense of Plutus).
class AsEvaluationFailure err where
    _EvaluationFailure :: Prism' err ()

evaluationFailure :: AsEvaluationFailure err => err
evaluationFailure = _EvaluationFailure # ()

-- | Construct a 'Prism' focusing on the @*EvaluationFailure@ part of @err@ by taking
-- that @*EvaluationFailure@ and
--
-- 1. returning it for the setter part of the prism
-- 2. checking the error for equality with @*EvaluationFailure@ for the opposite direction.
_EvaluationFailureVia :: Eq err => err -> Prism' err ()
_EvaluationFailureVia failure = prism (const failure) $ \a -> when (a /= failure) $ Left a

-- | The parameterized type of results various evaluation engines return.
-- On the PLC side this becomes (via @makeKnown@) either a call to 'Error' or
-- a value of the PLC counterpart of type @a@.
data EvaluationResult a
    = EvaluationSuccess a
    | EvaluationFailure
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable, NFData)

-- This and the next one are two instances that allow us to write the following:
--
-- >>> import Control.Monad.Error.Lens
-- >>> throwing_ _EvaluationFailure :: EvaluationResult Bool
-- EvaluationFailure
instance AsEvaluationFailure () where
    _EvaluationFailure = id

instance MonadError () EvaluationResult where
    throwError () = EvaluationFailure

    catchError EvaluationFailure f = f ()
    catchError x                 _ = x

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
    prettyBy config (EvaluationSuccess x) = prettyBy config x
    prettyBy _      EvaluationFailure     = "Failure"

instance PrettyClassic a => Pretty (EvaluationResult a) where
    pretty = prettyClassicDef

-- | Check whether an 'EvaluationResult' is an 'EvaluationSuccess'.
isEvaluationSuccess :: EvaluationResult a -> Bool
isEvaluationSuccess = not . null

-- | Check whether an 'EvaluationResult' is an 'EvaluationFailure'.
isEvaluationFailure :: EvaluationResult a -> Bool
isEvaluationFailure = null
