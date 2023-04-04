-- editorconfig-checker-disable-file
-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Evaluation.Machine.Exception
    ( UnliftingError (..)
    , AsUnliftingError (..)
    , KnownTypeError (..)
    , MachineError (..)
    , AsMachineError (..)
    , EvaluationError (..)
    , AsEvaluationError (..)
    , ErrorWithCause (..)
    , EvaluationException
    , throwNotAConstant
    , throwing
    , throwing_
    , throwingWithCause
    , extractEvaluationResult
    , unsafeExtractEvaluationResult
    ) where

import PlutusPrelude

import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Control.Lens
import Control.Monad.Error.Lens (throwing, throwing_)
import Control.Monad.Except
import Data.Either.Extras
import Data.String (IsString)
import Data.Text (Text)
import Data.Word (Word64)
import Prettyprinter

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving stock (Show, Eq)
    deriving newtype (IsString, Semigroup, NFData)

-- | The type of errors that 'readKnown' and 'makeKnown' can return.
data KnownTypeError
    = KnownTypeUnliftingError !UnliftingError
    | KnownTypeEvaluationFailure
    deriving stock (Eq)

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
    | UnknownBuiltin fun
    | NonConstrScrutinized
    | MissingCaseBranch Word64
    deriving stock (Show, Eq, Functor, Generic)
    deriving anyclass (NFData)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError user internal
    = InternalEvaluationError !internal
      -- ^ Indicates bugs.
    | UserEvaluationError !user
      -- ^ Indicates user errors.
    deriving stock (Show, Eq, Functor, Generic)
    deriving anyclass (NFData)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''KnownTypeError
    , ''MachineError
    , ''EvaluationError
    ]

instance AsUnliftingError KnownTypeError where
    _UnliftingError = _KnownTypeUnliftingError
instance AsEvaluationFailure KnownTypeError where
    _EvaluationFailure = _EvaluationFailureVia KnownTypeEvaluationFailure

instance internal ~ MachineError fun => AsMachineError (EvaluationError user internal) fun where
    _MachineError = _InternalEvaluationError
instance AsUnliftingError internal => AsUnliftingError (EvaluationError user internal) where
    _UnliftingError = _InternalEvaluationError . _UnliftingError
instance AsUnliftingError (MachineError fun) where
    _UnliftingError = _UnliftingMachineError
instance AsEvaluationFailure user => AsEvaluationFailure (EvaluationError user internal) where
    _EvaluationFailure = _UserEvaluationError . _EvaluationFailure

-- | An error and (optionally) what caused it.
data ErrorWithCause err cause = ErrorWithCause
    { _ewcError :: !err
    , _ewcCause :: !(Maybe cause)
    } deriving stock (Eq, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

instance Bifunctor ErrorWithCause where
    bimap f g (ErrorWithCause err cause) = ErrorWithCause (f err) (g <$> cause)

instance AsEvaluationFailure err => AsEvaluationFailure (ErrorWithCause err cause) where
    _EvaluationFailure = iso _ewcError (flip ErrorWithCause Nothing) . _EvaluationFailure

instance (Pretty err, Pretty cause) => Pretty (ErrorWithCause err cause) where
    pretty (ErrorWithCause e c) = pretty e <+> "caused by:" <+> pretty c

type EvaluationException user internal =
    ErrorWithCause (EvaluationError user internal)

throwNotAConstant :: MonadError KnownTypeError m => m void
throwNotAConstant = throwError $ KnownTypeUnliftingError "Not a constant"
{-# INLINE throwNotAConstant #-}

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
builtin evaluation, or exceeding the gas limit).  This is used to
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
unsafeExtractEvaluationResult = unsafeFromEither . extractEvaluationResult

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a value:", hardline
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
    prettyBy _      (UnliftingMachineError unliftingError)  =
        pretty unliftingError
    prettyBy _      (UnknownBuiltin fun)                  =
        "Encountered an unknown built-in function:" <+> pretty fun
    prettyBy _      NonConstrScrutinized =
        "A non-constructor value was scrutinitzed in a case expression"
    prettyBy _      (MissingCaseBranch i) =
        "Case expression missing the branch required by the scrutinee tag:" <+> pretty i

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

instance (PrettyBy config cause, PrettyBy config err) =>
            PrettyBy config (ErrorWithCause err cause) where
    prettyBy config (ErrorWithCause err mayCause) =
        "An error has occurred: " <+> prettyBy config err <>
            case mayCause of
                Nothing    -> mempty
                Just cause -> hardline <> "Caused by:" <+> prettyBy config cause

instance (PrettyPlc cause, PrettyPlc err) =>
            Show (ErrorWithCause err cause) where
    show = render . prettyPlcReadableDebug

deriving anyclass instance
    (PrettyPlc cause, PrettyPlc err, Typeable cause, Typeable err) => Exception (ErrorWithCause err cause)
