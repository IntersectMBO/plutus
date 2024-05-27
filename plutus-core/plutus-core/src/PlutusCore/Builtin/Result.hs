{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}

module PlutusCore.Builtin.Result
    ( EvaluationError (..)
    , AsEvaluationError (..)
    , UnliftingError (..)
    , BuiltinError (..)
    , BuiltinResult (..)
    , AsUnliftingError (..)
    , AsBuiltinError (..)
    , AsBuiltinResult (..)
    , throwNotAConstant
    , withLogs
    , throwing
    , throwing_
    ) where

import PlutusPrelude

import PlutusCore.Builtin.Emitter
import PlutusCore.Evaluation.Error
import PlutusCore.Evaluation.Result

import Control.Lens
import Control.Monad.Error.Lens (throwing, throwing_)
import Control.Monad.Except
import Data.DList (DList)
import Data.Text (Text)
import Prettyprinter

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError = MkUnliftingError
    { unUnliftingError :: EvaluationError Text Text
    } deriving stock (Show, Eq)
      deriving newtype (NFData)

-- | The type of errors that 'readKnown' and 'makeKnown' can return.
data BuiltinError
    = BuiltinUnliftingError !UnliftingError
    | BuiltinEvaluationFailure
    deriving stock (Show, Eq)

-- | The monad that 'makeKnown' runs in.
-- Equivalent to @ExceptT BuiltinError Emitter@, except optimized in two ways:
--
-- 1. everything is strict
-- 2. has the 'BuiltinSuccess' constructor that is used for returning a value with no logs
--    attached, which is the most common case for us, so it helps a lot not to construct and
--    deconstruct a redundant tuple
--
-- Moving from @ExceptT BuiltinError Emitter@ to this data type gave us a speedup of 8% of total
-- evaluation time.
--
-- Logs are represented as a 'DList', because we don't particularly care about the efficiency of
-- logging, since there's no logging on the chain and builtins don't emit much anyway. Otherwise
-- we'd have to use @text-builder@ or @text-builder-linear@ or something of this sort.
data BuiltinResult a
    = BuiltinFailure (DList Text) BuiltinError
    | BuiltinSuccess a
    | BuiltinSuccessWithLogs (DList Text) a
    deriving stock (Show, Foldable)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''BuiltinError
    , ''BuiltinResult
    ]

instance AsEvaluationError UnliftingError Text Text where
    _EvaluationError = _UnliftingError . _EvaluationError

instance (AsUnliftingError operational, AsUnliftingError structural) =>
        AsUnliftingError (EvaluationError operational structural) where
    _UnliftingError = undefined -- prism' (_ . unUnliftingError) _

instance AsUnliftingError BuiltinError where
    _UnliftingError = _BuiltinUnliftingError
    {-# INLINE _UnliftingError #-}

instance AsEvaluationFailure BuiltinError where
    _EvaluationFailure = _EvaluationFailureVia BuiltinEvaluationFailure
    {-# INLINE _EvaluationFailure #-}

-- >>> import PlutusCore.Evaluation.Result
-- >>> evaluationFailure :: BuiltinResult Bool
-- BuiltinFailure (fromList []) BuiltinEvaluationFailure
--
-- >>> import Control.Lens
-- >>> let res = BuiltinFailure (pure mempty) evaluationFailure :: BuiltinResult Bool
-- >>> matching _EvaluationFailure res
-- Right ()
--
-- >>> matching _BuiltinFailure $ BuiltinSuccess True
-- Left (BuiltinSuccess True)
instance AsEvaluationFailure (BuiltinResult a) where
    _EvaluationFailure = _BuiltinFailure . iso (\_ -> ()) (\_ -> pure evaluationFailure)
    {-# INLINE _EvaluationFailure #-}

instance MonadEmitter BuiltinResult where
    emit txt = BuiltinSuccessWithLogs (pure txt) ()
    {-# INLINE emit #-}

instance Pretty UnliftingError where
    pretty (MkUnliftingError err) = fold
        [ "Could not unlift a value:", hardline
        , pretty err
        ]

instance Pretty BuiltinError where
    pretty (BuiltinUnliftingError err) = "Builtin evaluation failure:" <+> pretty err
    pretty BuiltinEvaluationFailure    = "Builtin evaluation failure"

throwNotAConstant :: MonadError BuiltinError m => m void
throwNotAConstant =
    throwError . BuiltinUnliftingError . MkUnliftingError $
        StructuralEvaluationError "Not a constant"
{-# INLINE throwNotAConstant #-}

-- | Prepend logs to a 'BuiltinResult' computation.
withLogs :: DList Text -> BuiltinResult a -> BuiltinResult a
withLogs logs1 = \case
    BuiltinFailure logs2 err       -> BuiltinFailure (logs1 <> logs2) err
    BuiltinSuccess x               -> BuiltinSuccessWithLogs logs1 x
    BuiltinSuccessWithLogs logs2 x -> BuiltinSuccessWithLogs (logs1 <> logs2) x
{-# INLINE withLogs #-}

instance Functor BuiltinResult where
    fmap _ (BuiltinFailure logs err)       = BuiltinFailure logs err
    fmap f (BuiltinSuccess x)              = BuiltinSuccess (f x)
    fmap f (BuiltinSuccessWithLogs logs x) = BuiltinSuccessWithLogs logs (f x)
    {-# INLINE fmap #-}

    -- Written out explicitly just in case.
    _ <$ BuiltinFailure logs err       = BuiltinFailure logs err
    x <$ BuiltinSuccess _              = BuiltinSuccess x
    x <$ BuiltinSuccessWithLogs logs _ = BuiltinSuccessWithLogs logs x
    {-# INLINE (<$) #-}

instance Applicative BuiltinResult where
    pure = BuiltinSuccess
    {-# INLINE pure #-}

    BuiltinFailure logs err       <*> _ = BuiltinFailure logs err
    BuiltinSuccess f              <*> a = fmap f a
    BuiltinSuccessWithLogs logs f <*> a = withLogs logs $ fmap f a
    {-# INLINE (<*>) #-}

    -- Better than the default implementation, because the value in the 'BuiltinSuccess' case
    -- doesn't need to be retained.
    BuiltinFailure logs err       *> _ = BuiltinFailure logs err
    BuiltinSuccess _              *> b = b
    BuiltinSuccessWithLogs logs _ *> b = withLogs logs b
    {-# INLINE (*>) #-}

instance Monad BuiltinResult where
    BuiltinFailure logs err       >>= _ = BuiltinFailure logs err
    BuiltinSuccess x              >>= f = f x
    BuiltinSuccessWithLogs logs x >>= f = withLogs logs $ f x
    {-# INLINE (>>=) #-}

    (>>) = (*>)
    {-# INLINE (>>) #-}
