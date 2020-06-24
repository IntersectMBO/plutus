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

import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Pretty

import           Control.Lens
import           Control.Monad.Except
import           Data.String                           (IsString)
import           Data.Text                             (Text)
import           Data.Text.Prettyprint.Doc

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString, Semigroup)

-- | The type of constant applications errors (i.e. errors that may occur during evaluation of
-- a builtin function applied to some arguments).
data ConstAppError term
    = ExcessArgumentsConstAppError [term]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq)

-- | Errors which can occur during a run of an abstract machine.
data MachineError term err
    = NonPrimitiveInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonPrimitiveApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError (ConstAppError term)
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | OtherMachineError err
    deriving (Show, Eq)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError term internal user
    = InternalEvaluationError (MachineError term internal)
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

instance AsMachineError (EvaluationError term internal user) term internal where
    _MachineError = _InternalEvaluationError
instance AsConstAppError (MachineError term err) term where
    _ConstAppError = _ConstAppMachineError
instance AsConstAppError (EvaluationError term internal user) term where
    _ConstAppError = _InternalEvaluationError . _ConstAppMachineError
instance AsUnliftingError (ConstAppError term) where
    _UnliftingError = _UnliftingConstAppError
instance AsUnliftingError (EvaluationError term internal user) where
    _UnliftingError = _InternalEvaluationError . _UnliftingConstAppError
instance AsUnliftingError (MachineError term err) where
    _UnliftingError = _ConstAppMachineError . _UnliftingConstAppError

-- | An error and (optionally) what caused it.
data ErrorWithCause term err
    = ErrorWithCause err (Maybe term)
    deriving (Eq, Functor)

type MachineException term internal = ErrorWithCause term (MachineError term internal)
type EvaluationException term internal user = ErrorWithCause term (EvaluationError term internal user)

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    :: MonadError (ErrorWithCause term e) m
    => AReview e t -> t -> Maybe term -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t

-- | Turn any 'UserEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException term internal user) a
    -> Either (MachineException term internal) (EvaluationResult a)
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
    prettyBy config (ExcessArgumentsConstAppError args) = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err

instance (PrettyBy config term, HasPrettyDefaults config ~ 'True, Pretty err) =>
            PrettyBy config (MachineError term err) where
    prettyBy _      NonPrimitiveInstantiationMachineError =
        "Cannot reduce a not immediately reducible type instantiation."
    prettyBy _      NonWrapUnwrappedMachineError          =
        "Cannot unwrap a not wrapped term."
    prettyBy _      NonPrimitiveApplicationMachineError   =
        "Cannot reduce a not immediately reducible application."
    prettyBy _      OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term."
    prettyBy config (ConstAppMachineError constAppError)  =
        prettyBy config constAppError
    prettyBy _      (OtherMachineError err)               =
        pretty err

instance
        ( PrettyBy config term, HasPrettyDefaults config ~ 'True
        , Pretty internal, Pretty user
        ) => PrettyBy config (EvaluationError term internal user) where
    prettyBy config (InternalEvaluationError err) = fold
        [ "Internal error:", hardline
        , prettyBy config err
        ]
    prettyBy _      (UserEvaluationError err) = fold
        [ "User error:", hardline
        , pretty err
        ]

instance (PrettyBy config term, PrettyBy config err) =>
            PrettyBy config (ErrorWithCause term err) where
    prettyBy config (ErrorWithCause err mayCause) =
        "An error has occurred: " <+> prettyBy config err <>
            case mayCause of
                Nothing    -> mempty
                Just cause -> hardline <> "Caused by:" <+> prettyBy config cause

instance (PrettyPlc term, PrettyPlc err) =>
            Show (ErrorWithCause term err) where
    show = render . prettyPlcReadableDebug

instance (PrettyPlc term, PrettyPlc err, Typeable term, Typeable err) =>
            Exception (ErrorWithCause term err)
