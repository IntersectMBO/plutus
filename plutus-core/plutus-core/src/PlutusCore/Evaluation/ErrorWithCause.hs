{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusCore.Evaluation.ErrorWithCause
    ( ErrorWithCause (..)
    , throwingWithCause
    , throwingWithCause_
    , throwBuiltinErrorWithCause
    ) where

import PlutusPrelude

import PlutusCore.Builtin.Result
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Control.Lens
import Control.Monad.Except
import Prettyprinter

-- | An error and (optionally) what caused it.
data ErrorWithCause err cause = ErrorWithCause
    { _ewcError :: !err
    , _ewcCause :: !(Maybe cause)
    } deriving stock (Eq, Functor, Foldable, Traversable, Generic)
      deriving anyclass (NFData)

instance Bifunctor ErrorWithCause where
    bimap f g (ErrorWithCause err cause) = ErrorWithCause (f err) (g <$> cause)
    {-# INLINE bimap #-}

instance AsEvaluationFailure err => AsEvaluationFailure (ErrorWithCause err cause) where
    _EvaluationFailure = iso _ewcError (flip ErrorWithCause Nothing) . _EvaluationFailure
    {-# INLINE _EvaluationFailure #-}

instance (Pretty err, Pretty cause) => Pretty (ErrorWithCause err cause) where
    pretty (ErrorWithCause e c) = pretty e <+> "caused by:" <+> pretty c

instance (PrettyBy config cause, PrettyBy config err) =>
            PrettyBy config (ErrorWithCause err cause) where
    prettyBy config (ErrorWithCause err mayCause) = fold
        [ "An error has occurred:"
        , hardline
        , prettyBy config err
        , case mayCause of
            Nothing    -> mempty
            Just cause -> hardline <> "Caused by:" <+> prettyBy config cause
        ]

instance (PrettyPlc cause, PrettyPlc err) =>
            Show (ErrorWithCause err cause) where
    show = render . prettyPlcReadableDebug

deriving anyclass instance (PrettyPlc cause, PrettyPlc err, Typeable cause, Typeable err) =>
    Exception (ErrorWithCause err cause)

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    -- Binds @exc@ so it can be used as a convenient parameter with @TypeApplications@.
    :: forall exc e t term m x. (exc ~ ErrorWithCause e term, MonadError exc m)
    => AReview e t -> t -> Maybe term -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t
{-# INLINE throwingWithCause #-}

-- | "Prismatically" throw a contentless error and its (optional) cause. 'throwingWithCause_' is to
-- 'throwingWithCause' as 'throwing_' is to 'throwing'.
throwingWithCause_
    -- Binds @exc@ so it can be used as a convenient parameter with @TypeApplications@.
    :: forall exc e term m x. (exc ~ ErrorWithCause e term, MonadError exc m)
    => AReview e () -> Maybe term -> m x
throwingWithCause_ l = throwingWithCause l ()
{-# INLINE throwingWithCause_ #-}

-- | Attach a @cause@ to a 'BuiltinError' and throw that.
-- Note that an evaluator might require the cause to be computed lazily for best performance on the
-- happy path, hence this function must not force its first argument.
-- TODO: wrap @cause@ in 'Lazy' once we have it.
throwBuiltinErrorWithCause
    :: ( MonadError (ErrorWithCause err cause) m
       , AsUnliftingEvaluationError err, AsEvaluationFailure err
       )
    => cause -> BuiltinError -> m void
throwBuiltinErrorWithCause cause = \case
    BuiltinUnliftingEvaluationError unlErr ->
        throwingWithCause _UnliftingEvaluationError unlErr $ Just cause
    BuiltinEvaluationFailure ->
        throwingWithCause_ _EvaluationFailure $ Just cause
{-# INLINE throwBuiltinErrorWithCause #-}
