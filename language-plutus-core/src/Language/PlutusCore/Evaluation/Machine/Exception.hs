-- | The exceptions that an abstract machine can throw.

-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

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

import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Lens
import           Control.Monad.Except
import           Data.String                           (IsString)
import           Data.Text                             (Text)

-- | When unlifting of a PLC term into a Haskell value fails, this error is thrown.
newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString, Semigroup)

-- | The type of constant applications errors (i.e. errors that may occur during evaluation of
-- a builtin function applied to some arguments).
data ConstAppError uni
    = ExcessArgumentsConstAppError [Value TyName Name uni ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq)

-- | Errors which can occur during a run of an abstract machine.
data MachineError uni err
    = NonPrimitiveInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedMachineError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonPrimitiveApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError (ConstAppError uni)
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | OtherMachineError err
    deriving (Show, Eq)

-- | The type of errors (all of them) which can occur during evaluation
-- (some are used-caused, some are internal).
data EvaluationError uni internal user
    = InternalEvaluationError (MachineError uni internal)
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

instance AsMachineError (EvaluationError uni internal user) uni internal where
    _MachineError = _InternalEvaluationError
instance AsConstAppError (MachineError uni err) uni where
    _ConstAppError = _ConstAppMachineError
instance AsConstAppError (EvaluationError uni internal user) uni where
    _ConstAppError = _InternalEvaluationError . _ConstAppMachineError
instance AsUnliftingError (ConstAppError uni) where
    _UnliftingError = _UnliftingConstAppError
instance AsUnliftingError (EvaluationError uni internal user) where
    _UnliftingError = _InternalEvaluationError . _UnliftingConstAppError
instance AsUnliftingError (MachineError uni err) where
    _UnliftingError = _ConstAppMachineError . _UnliftingConstAppError

-- | An error and (optionally) what caused it.
data ErrorWithCause uni err
    = ErrorWithCause err (Maybe (Term TyName Name uni ()))
    deriving (Eq, Functor)

type MachineException uni internal = ErrorWithCause uni (MachineError uni internal)
type EvaluationException uni internal user = ErrorWithCause uni (EvaluationError uni internal user)

-- | "Prismatically" throw an error and its (optional) cause.
throwingWithCause
    :: MonadError (ErrorWithCause uni e) m
    => AReview e t -> t -> Maybe (Term TyName Name uni ()) -> m x
throwingWithCause l t cause = reviews l (\e -> throwError $ ErrorWithCause e cause) t

-- | Turn any 'UserEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException uni internal user) a
    -> Either (MachineException uni internal) (EvaluationResult a)
extractEvaluationResult (Right term) = Right $ EvaluationSuccess term
extractEvaluationResult (Left (ErrorWithCause evalErr cause)) = case evalErr of
    InternalEvaluationError err -> Left $ ErrorWithCause err cause
    UserEvaluationError _       -> Right $ EvaluationFailure

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", hardline
        , pretty err
        ]

instance PrettyM config (Term TyName Name uni ()) => PrettyM config (ConstAppError uni) where
    prettyBy config (ExcessArgumentsConstAppError args) = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err

instance (Pretty err, PrettyM config (Term TyName Name uni ())) =>
            PrettyM config (MachineError uni err) where
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

instance (Pretty internal, Pretty user, PrettyM config (Term TyName Name uni ())) =>
            PrettyM config (EvaluationError uni internal user) where
    prettyBy config (InternalEvaluationError err) = fold
        [ "Internal error:", hardline
        , prettyBy config err
        ]
    prettyBy _      (UserEvaluationError err) = fold
        [ "User error:", hardline
        , pretty err
        ]

instance (PrettyM config (Term TyName Name uni ()), PrettyM config err) =>
            PrettyM config (ErrorWithCause uni err) where
    prettyBy config (ErrorWithCause err mayCause) =
        "An error has occurred: " <+> prettyBy config err <>
            case mayCause of
                Nothing    -> mempty
                Just cause -> hardline <> "Caused by:" <+> prettyBy config cause

instance (GShow uni, Closed uni, uni `Everywhere` Pretty, PrettyPlc err) =>
            Show (ErrorWithCause uni err) where
    show = docString . prettyPlcReadableDebug

instance (GShow uni, Closed uni, uni `Everywhere` Pretty, Typeable uni, PrettyPlc err, Typeable err) =>
            Exception (ErrorWithCause uni err)
