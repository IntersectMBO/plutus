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
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Evaluation.Machine.Exception
    ( UnliftingError (..)
    , AsUnliftingError (..)
    , BuiltinError (..)
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
    , unsafeToEvaluationResult
    ) where

import PlutusPrelude

import PlutusCore.Builtin.Result
import PlutusCore.Evaluation.ErrorWithCause
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Control.Lens
import Data.Either.Extras
import Data.Word (Word64)
import Prettyprinter

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

-- | The type of errors (all of them) which can occur during evaluation. TODO: explain
data EvaluationError operational structural
    = OperationalEvaluationError !operational
    | StructuralEvaluationError !structural
    deriving stock (Show, Eq, Functor, Generic)
    deriving anyclass (NFData)

mtraverse makeClassyPrisms
    [ ''MachineError
    , ''EvaluationError
    ]

instance structural ~ MachineError fun =>
        AsMachineError (EvaluationError operational structural) fun where
    _MachineError = _StructuralEvaluationError
instance AsUnliftingError structural =>
        AsUnliftingError (EvaluationError operational structural) where
    _UnliftingError = _StructuralEvaluationError . _UnliftingError
instance AsUnliftingError (MachineError fun) where
    _UnliftingError = _UnliftingMachineError
instance AsEvaluationFailure operational =>
        AsEvaluationFailure (EvaluationError operational structural) where
    _EvaluationFailure = _OperationalEvaluationError . _EvaluationFailure

type EvaluationException operational structural =
    ErrorWithCause (EvaluationError operational structural)

{- Note [Ignoring context in OperationalEvaluationError]
The OperationalEvaluationError error has a term argument, but
extractEvaluationResult just discards this and returns
EvaluationFailure.  This means that, for example, if we use the `plc`
command to execute a program containing a division by zero, plc exits
silently without reporting that anything has gone wrong (but returning
a non-zero exit code to the shell via `exitFailure`).  This is because
OperationalEvaluationError is used in cases when a PLC program itself goes
wrong (for example, a failure due to `(error)`, a failure during
builtin evaluation, or exceeding the gas limit).  This is used to
signal unsuccessful in validation and so is not regarded as a real
error; in contrast, machine errors, typechecking failures,
and so on are genuine errors and we report their context if available.
 -}

-- | Turn any 'OperationalEvaluationError' into an 'EvaluationFailure'.
extractEvaluationResult
    :: Either (EvaluationException operational structural term) a
    -> Either (ErrorWithCause structural term) (EvaluationResult a)
extractEvaluationResult (Right term) = Right $ EvaluationSuccess term
extractEvaluationResult (Left (ErrorWithCause evalErr cause)) = case evalErr of
    StructuralEvaluationError err -> Left  $ ErrorWithCause err cause
    OperationalEvaluationError _  -> Right $ EvaluationFailure

unsafeToEvaluationResult
    :: (PrettyPlc internal, PrettyPlc term, Typeable internal, Typeable term)
    => Either (EvaluationException user internal term) a
    -> EvaluationResult a
unsafeToEvaluationResult = unsafeFromEither . extractEvaluationResult

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
        "A non-constructor value was scrutinized in a case expression"
    prettyBy _      (MissingCaseBranch i) =
        "Case expression missing the branch required by the scrutinee tag:" <+> pretty i

instance
        ( HasPrettyDefaults config ~ 'True
        , Pretty operational, PrettyBy config structural
        ) => PrettyBy config (EvaluationError operational structural) where
    prettyBy _      (OperationalEvaluationError operational) = pretty operational
    prettyBy config (StructuralEvaluationError structural)   = prettyBy config structural
