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
    , MachineException
    , EvaluationException
    , throwingWithCause
    , extractEvaluationResult
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Common ()
import           Language.PlutusCore.Core.Type                   (BuiltinName)
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Pretty

import           Control.Lens
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
data ConstAppError term
    =  TooFewArgumentsConstAppError BuiltinName
    | TooManyArgumentsConstAppError BuiltinName [term]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq, Functor)

-- | Errors which can occur during a run of an abstract machine.
data MachineError err term
    = NonPolymorphicInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonFunctionalApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError (ConstAppError term)
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | UnexpectedBuiltinInstantiationMachineError
      -- ^ A builtin was instantiated when a term argument was expected
    | UnexpectedBuiltinTermArgumentMachineError
      -- ^ A term argument to a builtin was encountered when an instantiation was expected
    | EmptyBuiltinArityMachineError
      -- ^ We've reached a state where a builtin instantiation or application is attempted
      -- when the arity is zero. In the absence of nullary builtins, this should be impossible.
      -- See the machine implementations for details.
    | OtherMachineError err
    deriving (Show, Eq, Functor)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError internal user term
    = InternalEvaluationError (MachineError internal term)
      -- ^ Indicates bugs.
    | UserEvaluationError user
      -- ^ Indicates user errors.
    deriving (Show, Eq)

mtraverse makeClassyPrisms
    [ ''UnliftingError
    , ''ConstAppError
    , ''MachineError
    , ''EvaluationError
    ]

instance AsMachineError (EvaluationError internal user term) internal term where
    _MachineError = _InternalEvaluationError
instance AsConstAppError (MachineError err term) term where
    _ConstAppError = _ConstAppMachineError
instance AsConstAppError (EvaluationError internal user term) term where
    _ConstAppError = _InternalEvaluationError . _ConstAppMachineError
instance AsUnliftingError (ConstAppError term) where
    _UnliftingError = _UnliftingConstAppError
instance AsUnliftingError (EvaluationError internal user term) where
    _UnliftingError = _InternalEvaluationError . _UnliftingConstAppError
instance AsUnliftingError (MachineError err term) where
    _UnliftingError = _ConstAppMachineError . _UnliftingConstAppError

-- | An error and (optionally) what caused it.
data ErrorWithCause err term
    = ErrorWithCause err (Maybe term)
    deriving (Eq, Functor)

type MachineException internal term = ErrorWithCause (MachineError internal term) term
type EvaluationException internal user term = ErrorWithCause (EvaluationError internal user term) term

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    :: MonadError (ErrorWithCause e term) m
    => AReview e t -> t -> Maybe term -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t



{- [Note: Ignoring context in UserEvaluationError] The UserEvaluationError error
   has a term argument, but extractEvaluationResult just discards this and
   returns EvaluationFailure.  This means that, for example, if we use the `plc`
   command to execute a program containing a division by zero, plc exits
   silently without reporting that anything has gone wrong (but returning a
   non-zero exit code to the shell via `exitFailure`).  This is because
   UserEvaluationError is used in cases when a PLC program itself goes wrong
   (for example, a failure due to `(error)`, a failure during builtin
   evavluation, or exceeding the gas limit).  This is used to signal
   unsuccessful in validation and so is not regarded as a real error; in
   contrast, internal machine errors, typechecking failures, and so on are
   genuine errors and we report their context if available.
 -}

-- | Turn any 'UserEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException internal user term) a
    -> Either (MachineException internal term) (EvaluationResult a)
extractEvaluationResult (Right term) = Right $ EvaluationSuccess term
extractEvaluationResult (Left (ErrorWithCause evalErr cause)) = case evalErr of
    InternalEvaluationError err -> Left $ ErrorWithCause err cause
    UserEvaluationError _       -> Right $ EvaluationFailure

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", hardline
        , pretty err
        ]

instance (PrettyBy config term, HasPrettyDefaults config ~ 'True) =>
        PrettyBy config (ConstAppError term) where
    prettyBy _ (TooFewArgumentsConstAppError name) =
        "The constant" <+> pretty name <+> "was applied to too few arguments."
    prettyBy config (TooManyArgumentsConstAppError name args) = fold
        [ "The constant" <+> pretty name <+> "was applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err

instance (PrettyBy config term, HasPrettyDefaults config ~ 'True, Pretty err) =>
            PrettyBy config (MachineError err term) where
    prettyBy _      NonPolymorphicInstantiationMachineError =
        "Attempted to instantiate a non-polymorphic term."
    prettyBy _      NonWrapUnwrappedMachineError          =
        "Cannot unwrap a not wrapped term."
    prettyBy _      NonFunctionalApplicationMachineError   =
        "Attempted to apply a non-function."
    prettyBy _      OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term."
    prettyBy _      UnexpectedBuiltinInstantiationMachineError =
        "A builtin was instantiated when a term argument was expected "
    prettyBy _      UnexpectedBuiltinTermArgumentMachineError =
        "A buitlin received a term argument when an instantiation was expected"
    prettyBy _      EmptyBuiltinArityMachineError =
        "A builtin was applied to a term or type where no more arguments were expected"
    prettyBy config (ConstAppMachineError constAppError)  =
        prettyBy config constAppError
    prettyBy _      (OtherMachineError err)               =
        pretty err

instance
        ( PrettyBy config term, HasPrettyDefaults config ~ 'True
        , Pretty internal, Pretty user
        ) => PrettyBy config (EvaluationError internal user term) where
    prettyBy config (InternalEvaluationError err) = fold
        [ "Internal error:", hardline
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
