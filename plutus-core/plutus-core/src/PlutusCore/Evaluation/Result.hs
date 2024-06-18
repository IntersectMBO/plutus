-- | This module defines a common type various evaluation machine use to return their results.

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
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

import PlutusPrelude

import PlutusCore.Pretty

import Control.Lens
import Control.Monad.Except (MonadError, catchError, throwError)

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
{-# INLINE evaluationFailure #-}

-- | Construct a prism focusing on the @*EvaluationFailure@ part of @err@ by taking
-- that @*EvaluationFailure@ and
--
-- 1. returning it for the setter part of the prism
-- 2. checking the error for equality with @*EvaluationFailure@ for the opposite direction.
_EvaluationFailureVia :: Eq err => err -> Prism' err ()
_EvaluationFailureVia = only
{-# INLINE _EvaluationFailureVia #-}

-- | The parameterized type of results various evaluation engines return.
-- On the PLC side this becomes (via @makeKnown@) either a call to 'Error' or
-- a value of the PLC counterpart of type @a@.
data EvaluationResult a
    = EvaluationSuccess !a
    | EvaluationFailure
    deriving stock (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (NFData)

-- >>> evaluationFailure :: EvaluationResult Bool
-- EvaluationFailure
--
-- >>> import Control.Lens
-- >>> matching _EvaluationFailure (EvaluationFailure :: EvaluationResult Bool)
-- Right ()
--
-- >>> matching _EvaluationFailure $ EvaluationSuccess True
-- Left (EvaluationSuccess True)
instance AsEvaluationFailure (EvaluationResult a) where
    _EvaluationFailure = prism (const EvaluationFailure) $ \case
        a@EvaluationSuccess{} -> Left a
        EvaluationFailure     -> Right ()
    {-# INLINE _EvaluationFailure #-}

-- This and the next one are two instances that allow us to write the following:
--
-- >>> import Control.Monad.Error.Lens
-- >>> throwing_ _EvaluationFailure :: EvaluationResult Bool
-- EvaluationFailure
instance AsEvaluationFailure () where
    _EvaluationFailure = id
    {-# INLINE _EvaluationFailure #-}

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
    pretty = prettyClassicDef

-- | Check whether an 'EvaluationResult' is an 'EvaluationSuccess'.
isEvaluationSuccess :: EvaluationResult a -> Bool
isEvaluationSuccess = not . null

-- | Check whether an 'EvaluationResult' is an 'EvaluationFailure'.
isEvaluationFailure :: EvaluationResult a -> Bool
isEvaluationFailure = null
