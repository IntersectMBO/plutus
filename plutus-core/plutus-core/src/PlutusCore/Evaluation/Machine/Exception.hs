-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Evaluation.Machine.Exception
    ( UnliftingError (..)
    , AsUnliftingError (..)
    , MachineError (..)
    , AsMachineError (..)
    , EvaluationError (..)
    , AsEvaluationError (..)
    , ErrorWithCause (..)
    , EvaluationException
    , mapCauseInMachineException
    , throwing_
    , throwingWithCause
    , extractEvaluationResult
    , unsafeExtractEvaluationResult
    ) where

import           PlutusPrelude

import           PlutusCore.Core.Instance.Pretty.Common ()
import           PlutusCore.Evaluation.Result
import           PlutusCore.Pretty

import           Control.Lens
import           Control.Monad.Error.Lens               (throwing_)
import           Control.Monad.Except
import           Data.String                            (IsString)
import           Data.Text                              (Text)
import           Data.Text.Prettyprint.Doc
import           ErrorCode

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString, Semigroup, NFData)

-- | Errors which can occur during a run of an abstract machine.
data MachineError fun
    = NonPolymorphicInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonFunctionalApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | UnliftingMachineError UnliftingError
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | BuiltinTermArgumentExpectedMachineError
      -- ^ A builtin expected a term argument, but something else was received
    | UnexpectedBuiltinTermArgumentMachineError
      -- ^ A builtin received a term argument when something else was expected
    | EmptyBuiltinArityMachineError
      -- ^ We've reached a state where a builtin instantiation or application is attempted
      -- when the arity is zero. In the absence of nullary builtins, this should be impossible.
      -- See the machine implementations for details.
    | UnknownBuiltin fun
    deriving (Show, Eq, Functor, Generic, NFData)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError user internal
    = InternalEvaluationError internal
      -- ^ Indicates bugs.
    | UserEvaluationError user
      -- ^ Indicates user errors.
    deriving (Show, Eq, Functor, Generic, NFData)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''MachineError
    , ''EvaluationError
    ]

instance internal ~ MachineError fun => AsMachineError (EvaluationError user internal) fun where
    _MachineError = _InternalEvaluationError
instance AsUnliftingError internal => AsUnliftingError (EvaluationError user internal) where
    _UnliftingError = _InternalEvaluationError . _UnliftingError
instance AsUnliftingError (MachineError fun) where
    _UnliftingError = _UnliftingMachineError
instance AsEvaluationFailure user => AsEvaluationFailure (EvaluationError user internal) where
    _EvaluationFailure = _UserEvaluationError . _EvaluationFailure

-- | An error and (optionally) what caused it.
data ErrorWithCause err term = ErrorWithCause
    { _ewcError :: err
    , _ewcCause :: Maybe term
    } deriving (Eq, Functor, Foldable, Traversable, Generic, NFData)

instance Bifunctor ErrorWithCause where
    bimap f g (ErrorWithCause err cause) = ErrorWithCause (f err) (g <$> cause)

instance AsEvaluationFailure err => AsEvaluationFailure (ErrorWithCause err term) where
    _EvaluationFailure = iso _ewcError (flip ErrorWithCause Nothing) . _EvaluationFailure

instance (Pretty err, Pretty term) => Pretty (ErrorWithCause err term) where
    pretty (ErrorWithCause e c) = pretty e <+> "caused by:" <+> pretty c

type EvaluationException user internal =
    ErrorWithCause (EvaluationError user internal)

mapCauseInMachineException
    :: (term1 -> term2)
    -> EvaluationException user (MachineError fun) term1
    -> EvaluationException user (MachineError fun) term2
mapCauseInMachineException = fmap

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    -- Binds exc so it can be used as a convenient parameter with TypeApplications
    :: forall exc e t term m x
    . (exc ~ ErrorWithCause e term, MonadError exc m)
    => AReview e t -> t -> Maybe term -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t

{- Note [Ignoring context in UserEvaluationError]
The UserEvaluationError error has a term argument, but
extractEvaluationResult just discards this and returns
EvaluationFailure.  This means that, for example, if we use the `plc`
command to execute a program containing a division by zero, plc exits
silently without reporting that anything has gone wrong (but returning
a non-zero exit code to the shell via `exitFailure`).  This is because
UserEvaluationError is used in cases when a PLC program itself goes
wrong (for example, a failure due to `(error)`, a failure during
builtin evavluation, or exceeding the gas limit).  This is used to
signal unsuccessful in validation and so is not regarded as a real
error; in contrast, machine errors, typechecking failures,
and so on are genuine errors and we report their context if available.
 -}

-- | Turn any 'UserEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException user internal term) a
    -> Either (ErrorWithCause internal term) (EvaluationResult a)
extractEvaluationResult (Right term) = Right $ EvaluationSuccess term
extractEvaluationResult (Left (ErrorWithCause evalErr cause)) = case evalErr of
    InternalEvaluationError err -> Left  $ ErrorWithCause err cause
    UserEvaluationError _       -> Right $ EvaluationFailure

unsafeExtractEvaluationResult
    :: (PrettyPlc internal, PrettyPlc term, Typeable internal, Typeable term)
    => Either (EvaluationException user internal term) a
    -> EvaluationResult a
unsafeExtractEvaluationResult = either throw id . extractEvaluationResult

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", hardline
        , pretty err
        ]

instance (HasPrettyDefaults config ~ 'True, Pretty fun) =>
            PrettyBy config (MachineError fun) where
    prettyBy _      NonPolymorphicInstantiationMachineError =
        "Attempted to instantiate a non-polymorphic term."
    prettyBy _      NonWrapUnwrappedMachineError          =
        "Cannot unwrap a not wrapped term."
    prettyBy _      NonFunctionalApplicationMachineError   =
        "Attempted to apply a non-function."
    prettyBy _      OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term"
    prettyBy _      BuiltinTermArgumentExpectedMachineError =
        "A builtin expected a term argument, but something else was received"
    prettyBy _      UnexpectedBuiltinTermArgumentMachineError =
        "A builtin received a term argument when something else was expected"
    prettyBy _      EmptyBuiltinArityMachineError =
        "A builtin was applied to a term or type where no more arguments were expected"
    prettyBy _      (UnliftingMachineError unliftingError)  =
        pretty unliftingError
    prettyBy _      (UnknownBuiltin fun)                  =
        "Encountered an unknown built-in function:" <+> pretty fun

instance
        ( HasPrettyDefaults config ~ 'True
        , PrettyBy config internal, Pretty user
        ) => PrettyBy config (EvaluationError user internal) where
    prettyBy config (InternalEvaluationError err) = fold
        [ "error:", hardline
        , prettyBy config err
        ]
    prettyBy _      (UserEvaluationError err) = fold
        [ "User error:", hardline
        , pretty err
        ]

instance (PrettyBy config term, PrettyBy config err) =>
            PrettyBy config (ErrorWithCause err term) where
    prettyBy config (ErrorWithCause err mayCause) =
        "An error has occurred: " <+> prettyBy config err <>
            case mayCause of
                Nothing    -> mempty
                Just cause -> hardline <> "Caused by:" <+> prettyBy config cause

instance (PrettyPlc term, PrettyPlc err) =>
            Show (ErrorWithCause err term) where
    show = render . prettyPlcReadableDebug

deriving anyclass instance
    (PrettyPlc term, PrettyPlc err, Typeable term, Typeable err) => Exception (ErrorWithCause err term)

instance HasErrorCode UnliftingError where
      errorCode        UnliftingErrorE {}        = ErrorCode 30

instance HasErrorCode (MachineError err) where
      errorCode        EmptyBuiltinArityMachineError {}             = ErrorCode 34
      errorCode        UnexpectedBuiltinTermArgumentMachineError {} = ErrorCode 33
      errorCode        BuiltinTermArgumentExpectedMachineError {}   = ErrorCode 32
      errorCode        OpenTermEvaluatedMachineError {}             = ErrorCode 27
      errorCode        NonFunctionalApplicationMachineError {}      = ErrorCode 26
      errorCode        NonWrapUnwrappedMachineError {}              = ErrorCode 25
      errorCode        NonPolymorphicInstantiationMachineError {}   = ErrorCode 24
      errorCode        (UnliftingMachineError e)                    = errorCode e
      errorCode        UnknownBuiltin {}                            = ErrorCode 17

instance (HasErrorCode user, HasErrorCode internal) => HasErrorCode (EvaluationError user internal) where
  errorCode (InternalEvaluationError e) = errorCode e
  errorCode (UserEvaluationError e)     = errorCode e

instance HasErrorCode err => HasErrorCode (ErrorWithCause err t) where
    errorCode (ErrorWithCause e _) = errorCode e
