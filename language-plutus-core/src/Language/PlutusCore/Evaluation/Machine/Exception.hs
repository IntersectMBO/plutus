-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
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

import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty

import           Control.Lens
import           Control.Monad.Except
import           Data.String                           (IsString)
import           Data.Text                             (Text)

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString)

-- | The type of constant applications errors (i.e. errors that may occur during evaluation of
-- a builtin function applied to some arguments).
data ConstAppError
    = ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq)

-- | Errors which can occur during a run of an abstract machine.
data MachineError err
    = NonPrimitiveInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonPrimitiveApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError ConstAppError
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | OtherMachineError err
    deriving (Show, Eq)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError internal user
    = InternalEvaluationError (MachineError internal)
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

instance AsMachineError (EvaluationError internal user) internal where
    _MachineError = _InternalEvaluationError
instance AsConstAppError (MachineError err) where
    _ConstAppError = _ConstAppMachineError
instance AsConstAppError (EvaluationError internal user) where
    _ConstAppError = _InternalEvaluationError . _ConstAppMachineError
instance AsUnliftingError ConstAppError where
    _UnliftingError = _UnliftingConstAppError
instance AsUnliftingError (EvaluationError internal user) where
    _UnliftingError = _InternalEvaluationError . _UnliftingConstAppError
instance AsUnliftingError (MachineError err) where
    _UnliftingError = _ConstAppMachineError . _UnliftingConstAppError

-- | An error and (optionally) what caused it.
data ErrorWithCause err
    = ErrorWithCause err (Maybe (Term TyName Name ()))
    deriving (Eq, Functor)

type MachineException internal = ErrorWithCause (MachineError internal)
type EvaluationException internal user = ErrorWithCause (EvaluationError internal user)

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    :: MonadError (ErrorWithCause e) m
    => AReview e t -> t -> Maybe (Term TyName Name ()) -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t

-- | Turn any 'UserEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException internal user) a
    -> Either (MachineException internal) (EvaluationResult a)
extractEvaluationResult (Right term) = Right $ EvaluationSuccess term
extractEvaluationResult (Left (ErrorWithCause evalErr cause)) = case evalErr of
    InternalEvaluationError err -> Left $ ErrorWithCause err cause
    UserEvaluationError _       -> Right $ EvaluationFailure

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", hardline
        , pretty err
        ]

instance PrettyBy config (Term TyName Name ()) => PrettyBy config ConstAppError where
    prettyBy config (ExcessArgumentsConstAppError args) = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err

instance (Pretty err, PrettyBy config (Term TyName Name ())) =>
            PrettyBy config (MachineError err) where
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

instance (Pretty internal, Pretty user, PrettyBy config (Term TyName Name ())) =>
            PrettyBy config (EvaluationError internal user) where
    prettyBy config (InternalEvaluationError err) = fold
        [ "An internal error has occurred:", hardline
        , prettyBy config err
        ]
    prettyBy _      (UserEvaluationError err) = fold
        [ "A user error has occurred:", hardline
        , pretty err
        ]

instance PrettyPlc err => Show (ErrorWithCause err) where
    show (ErrorWithCause err mayCause) = fold
        [ "An error has occurred: ", docString $ prettyPlcReadableDebug err
        , case mayCause of
            Nothing    -> ""
            Just cause -> "\nCaused by: " ++ docString (prettyPlcReadableDebug cause)
        ]

instance (PrettyPlc err, Typeable err) => Exception (ErrorWithCause err)
