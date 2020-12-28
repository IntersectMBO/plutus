-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Evaluation.Machine.Exception
    ( UnliftingError (..)
    , AsUnliftingError (..)
    , ConstAppError (..)
    , AsConstAppError (..)
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
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Pretty

import           Control.Lens
import           Control.Monad.Error.Lens                        (throwing_)
import           Control.Monad.Except
import           Data.String                                     (IsString)
import           Data.Text                                       (Text)
import           Data.Text.Prettyprint.Doc

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString, Semigroup)

-- | The type of constant applications errors (i.e. errors that may occur during evaluation of
-- a builtin function applied to some arguments).
data ConstAppError fun term
    = TooFewArgumentsConstAppError fun
    | TooManyArgumentsConstAppError fun [term]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq, Functor)

-- | Errors which can occur during a run of an abstract machine.
data MachineError fun term
    = NonPolymorphicInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonFunctionalApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError (ConstAppError fun term)
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
    deriving (Show, Eq, Functor)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError user internal
    = InternalEvaluationError internal
      -- ^ Indicates bugs.
    | UserEvaluationError user
      -- ^ Indicates user errors.
    deriving (Show, Eq, Functor)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''ConstAppError
    , ''MachineError
    , ''EvaluationError
    ]

instance internal ~ MachineError fun term => AsMachineError (EvaluationError user internal) fun term where
    _MachineError = _InternalEvaluationError
instance AsConstAppError (MachineError fun term) fun term where
    _ConstAppError = _ConstAppMachineError
instance internal ~ MachineError fun term => AsConstAppError (EvaluationError user internal) fun term where
    _ConstAppError = _InternalEvaluationError . _ConstAppMachineError
instance AsUnliftingError (ConstAppError fun term) where
    _UnliftingError = _UnliftingConstAppError
instance AsUnliftingError internal => AsUnliftingError (EvaluationError user internal) where
    _UnliftingError = _InternalEvaluationError . _UnliftingError
instance AsUnliftingError (MachineError fun term) where
    _UnliftingError = _ConstAppMachineError . _UnliftingConstAppError
instance AsEvaluationFailure user => AsEvaluationFailure (EvaluationError user internal) where
    _EvaluationFailure = _UserEvaluationError . _EvaluationFailure

-- | An error and (optionally) what caused it.
data ErrorWithCause err term = ErrorWithCause
    { _ewcError :: err
    , _ewcCause :: Maybe term
    } deriving (Eq, Functor)

instance Bifunctor ErrorWithCause where
    bimap f g (ErrorWithCause err cause) = ErrorWithCause (f err) (g <$> cause)

instance AsEvaluationFailure err => AsEvaluationFailure (ErrorWithCause err term) where
    _EvaluationFailure = iso _ewcError (flip ErrorWithCause Nothing) . _EvaluationFailure

type EvaluationException user internal =
    ErrorWithCause (EvaluationError user internal)

mapCauseInMachineException
    :: (term1 -> term2)
    -> EvaluationException user (MachineError fun term1) term1
    -> EvaluationException user (MachineError fun term2) term2
mapCauseInMachineException f = bimap (fmap (fmap f)) f

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    :: MonadError (ErrorWithCause e term) m
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

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", hardline
        , pretty err
        ]

instance (PrettyBy config term, HasPrettyDefaults config ~ 'True, Pretty fun) =>
        PrettyBy config (ConstAppError fun term) where
    prettyBy _ (TooFewArgumentsConstAppError name) =
        "The constant" <+> pretty name <+> "was applied to too few arguments."
    prettyBy config (TooManyArgumentsConstAppError name args) = fold
        [ "The constant" <+> pretty name <+> "was applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err

instance (PrettyBy config term, HasPrettyDefaults config ~ 'True, Pretty fun) =>
            PrettyBy config (MachineError fun term) where
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
    prettyBy config (ConstAppMachineError constAppError)  =
        prettyBy config constAppError
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

instance (PrettyPlc term, PrettyPlc err, Typeable term, Typeable err) =>
            Exception (ErrorWithCause err term)
