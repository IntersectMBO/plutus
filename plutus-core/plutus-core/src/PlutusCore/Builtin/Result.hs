-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StrictData             #-}
{-# LANGUAGE TemplateHaskell        #-}

module PlutusCore.Builtin.Result
    ( EvaluationError (..)
    , AsEvaluationError (..)
    , UnliftingError (..)
    , UnliftingEvaluationError (..)
    , BuiltinError (..)
    , BuiltinResult (..)
    , AsUnliftingEvaluationError (..)
    , AsUnliftingError (..)
    , AsBuiltinError (..)
    , AsBuiltinResult (..)
    , _UnliftingErrorVia
    , _StructuralUnliftingError
    , _OperationalUnliftingError
    , throwNotAConstant
    , throwUnderTypeError
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
import Data.Bitraversable
import Data.DList (DList)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as Text
import Prettyprinter

-- | The error message part of an 'UnliftingEvaluationError'.
newtype UnliftingError = MkUnliftingError
    { unUnliftingError :: Text
    } deriving stock (Show, Eq)
      deriving newtype (IsString, Semigroup, Monoid, NFData)

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingEvaluationError = MkUnliftingEvaluationError
    { unUnliftingEvaluationError :: EvaluationError UnliftingError UnliftingError
    } deriving stock (Show, Eq)
      deriving newtype (NFData)

-- | The type of errors that 'readKnown' and 'makeKnown' can return.
data BuiltinError
    = BuiltinUnliftingEvaluationError UnliftingEvaluationError
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
    = -- 'BuiltinSuccess' is the first constructor to make it a bit more likely for GHC to
      -- branch-predict it (which is something that we want, because most builtins return this
      -- constructor). It is however not guaranteed that GHC will predict it, because even though
      -- it's likely going to be a recursive case (it certainly is in the CEK machine) and thus the
      -- constructor has precedence over 'BuiltinFailure', it doesn't have precedence over
      -- 'BuiltinSuccessWithLogs', since that case is equally likely to be recursive.
      --
      -- Unfortunately, GHC doesn't offer any explicit control over branch-prediction (see this
      -- ticket: https://gitlab.haskell.org/ghc/ghc/-/issues/849), so relying on hope is the best we
      -- can do here.
      BuiltinSuccess a
    | BuiltinSuccessWithLogs (DList Text) a
    | BuiltinFailure (DList Text) BuiltinError
    deriving stock (Show, Foldable)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''UnliftingEvaluationError
    , ''BuiltinError
    , ''BuiltinResult
    ]

instance AsEvaluationError UnliftingEvaluationError UnliftingError UnliftingError where
    _EvaluationError = coerced
    {-# INLINE _EvaluationError #-}

-- | An 'UnliftingEvaluationError' /is/ an 'EvaluationError', hence for this instance we only
-- require both @operational@ and @structural@ to have '_UnliftingError' prisms, so that we can
-- handle both the cases pointwisely.
instance (AsUnliftingError operational, AsUnliftingError structural) =>
        AsUnliftingEvaluationError (EvaluationError operational structural) where
    _UnliftingEvaluationError = go . coerced where
        go =
            prism'
                (bimap
                    (review _UnliftingError)
                    (review _UnliftingError))
                (bitraverse
                    (reoption . matching _UnliftingError)
                    (reoption . matching _UnliftingError))
    {-# INLINE _UnliftingEvaluationError #-}

instance AsUnliftingEvaluationError BuiltinError where
    _UnliftingEvaluationError = _BuiltinUnliftingEvaluationError . _UnliftingEvaluationError
    {-# INLINE _UnliftingEvaluationError #-}

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

instance MonadFail BuiltinResult where
    fail err = BuiltinFailure (pure $ Text.pack err) BuiltinEvaluationFailure
    {-# INLINE fail #-}

instance Pretty UnliftingError where
    pretty (MkUnliftingError err) = fold
        [ "Could not unlift a value:", hardline
        , pretty err
        ]

deriving newtype instance Pretty UnliftingEvaluationError

instance Pretty BuiltinError where
    pretty (BuiltinUnliftingEvaluationError err) = "Builtin evaluation failure:" <+> pretty err
    pretty BuiltinEvaluationFailure              = "Builtin evaluation failure"

{- Note [INLINE and OPAQUE on error-related definitions]
We mark error-related definitions such as prisms like '_StructuralUnliftingError' and regular
functions like 'throwNotAConstant' with @INLINE@, because this produces significantly less cluttered
GHC Core. Not doing so results in 20+% larger Core for builtins.

However in a few specific cases we use @OPAQUE@ instead to get tighter Core. @OPAQUE@ is the same as
@NOINLINE@ except the former _actually_ prevents GHC from inlining the definition unlike the latter.
See this for details: https://github.com/ghc-proposals/ghc-proposals/blob/5577fd008924de8d89cfa9855fa454512e7dcc75/proposals/0415-opaque-pragma.rst

It's hard to predict where @OPAQUE@ instead of @INLINE@ will help to make GHC Core tidier, so it's
mostly just looking into the Core and seeing where there's obvious duplication that can be removed.
Such cases tend to be functions returning a value of a concrete error type (as opposed to a type
variable).
-}

-- See Note [Ignoring context in OperationalEvaluationError].
-- | Construct a prism focusing on the @*EvaluationFailure@ part of @err@ by taking
-- that @*EvaluationFailure@ and
--
-- 1. pretty-printing and embedding it into an 'UnliftingError' for the setter part of the prism
-- 2. returning it directly for the opposite direction (there's no other way to convert an
--    'UnliftingError' to an evaluation failure, since the latter doesn't carry any content)
--
-- This is useful for providing 'AsUnliftingError' instances for types such as 'CkUserError' and
-- 'CekUserError'.
_UnliftingErrorVia :: Pretty err => err -> Prism' err UnliftingError
_UnliftingErrorVia err = iso (MkUnliftingError . display) (const err)
{-# INLINE _UnliftingErrorVia #-}

_StructuralUnliftingError :: AsBuiltinError err => Prism' err UnliftingError
_StructuralUnliftingError = _BuiltinUnliftingEvaluationError . _StructuralEvaluationError
{-# INLINE _StructuralUnliftingError #-}

_OperationalUnliftingError :: AsBuiltinError err => Prism' err UnliftingError
_OperationalUnliftingError = _BuiltinUnliftingEvaluationError . _OperationalEvaluationError
{-# INLINE _OperationalUnliftingError #-}

throwNotAConstant :: MonadError BuiltinError m => m void
throwNotAConstant = throwing _StructuralUnliftingError "Not a constant"
{-# INLINE throwNotAConstant #-}

throwUnderTypeError :: MonadError BuiltinError m => m void
throwUnderTypeError = throwing _StructuralUnliftingError "Panic: 'TypeError' was bypassed"
{-# INLINE throwUnderTypeError #-}

-- | Prepend logs to a 'BuiltinResult' computation.
withLogs :: DList Text -> BuiltinResult a -> BuiltinResult a
withLogs logs1 = \case
    BuiltinSuccess x               -> BuiltinSuccessWithLogs logs1 x
    BuiltinSuccessWithLogs logs2 x -> BuiltinSuccessWithLogs (logs1 <> logs2) x
    BuiltinFailure logs2 err       -> BuiltinFailure (logs1 <> logs2) err
{-# INLINE withLogs #-}

instance Functor BuiltinResult where
    fmap f (BuiltinSuccess x)              = BuiltinSuccess (f x)
    fmap f (BuiltinSuccessWithLogs logs x) = BuiltinSuccessWithLogs logs (f x)
    fmap _ (BuiltinFailure logs err)       = BuiltinFailure logs err
    {-# INLINE fmap #-}

    -- Written out explicitly just in case.
    x <$ BuiltinSuccess _              = BuiltinSuccess x
    x <$ BuiltinSuccessWithLogs logs _ = BuiltinSuccessWithLogs logs x
    _ <$ BuiltinFailure logs err       = BuiltinFailure logs err
    {-# INLINE (<$) #-}

instance Applicative BuiltinResult where
    pure = BuiltinSuccess
    {-# INLINE pure #-}

    BuiltinSuccess f              <*> a = fmap f a
    BuiltinSuccessWithLogs logs f <*> a = withLogs logs $ fmap f a
    BuiltinFailure logs err       <*> _ = BuiltinFailure logs err
    {-# INLINE (<*>) #-}

    -- Better than the default implementation, because the value in the 'BuiltinSuccess' case
    -- doesn't need to be retained.
    BuiltinSuccess _              *> b = b
    BuiltinSuccessWithLogs logs _ *> b = withLogs logs b
    BuiltinFailure logs err       *> _ = BuiltinFailure logs err
    {-# INLINE (*>) #-}

instance Monad BuiltinResult where
    BuiltinSuccess x              >>= f = f x
    BuiltinSuccessWithLogs logs x >>= f = withLogs logs $ f x
    BuiltinFailure logs err       >>= _ = BuiltinFailure logs err
    {-# INLINE (>>=) #-}

    (>>) = (*>)
    {-# INLINE (>>) #-}

-- | 'throwError' puts every operational unlifting error into the 'BuiltinFailure' logs. This is to
-- compensate for the historical lack of error message content in operational errors (structural
-- ones don't have this problem) in our evaluators (the CK and CEK machines). It would be better to
-- fix the underlying issue and allow operational evaluation errors to carry some form of content,
-- but for now we just fix the symptom in order for the end user to see the error message that they
-- are supposed to see. The fix even makes some sense: what we do here is we emulate logging when
-- the thrown unlifting error is an operational one, i.e. this is similar to what some builtins do
-- manually (like when a crypto builtin fails and puts info about the failure into the logs).
instance MonadError BuiltinError BuiltinResult where
    throwError builtinErr = BuiltinFailure operationalLogs builtinErr where
        operationalLogs = case builtinErr of
            BuiltinUnliftingEvaluationError
                (MkUnliftingEvaluationError
                    (OperationalEvaluationError
                        (MkUnliftingError operationalErr))) -> pure operationalErr
            _ -> mempty
    {-# INLINE throwError #-}

    -- Throwing logs out is lame, but embedding them into the error would be weird, since that
    -- would change the error. Not that any of that matters, we only implement this because it's a
    -- method of 'MonadError' and we can't not implement it.
    --
    -- We could make it @MonadError (DList Text, BuiltinError)@, but logs are arbitrary and are not
    -- necessarily an inherent part of an error, so preserving them is as questionable as not doing
    -- so.
    BuiltinFailure _ err `catchError` f = f err
    res                  `catchError` _ = res
    {-# INLINE catchError #-}
