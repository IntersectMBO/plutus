{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- editorconfig-checker-disable-file
-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- | The exceptions that an abstract machine can throw.
module PlutusCore.Evaluation.Machine.Exception
  ( UnliftingError (..)
  , BuiltinError (..)
  , MachineError (..)
  , EvaluationError (..)
  , ErrorWithCause (..)
  , EvaluationException
  , notAConstant
  , throwErrorWithCause
  , splitStructuralOperational
  , unsafeSplitStructuralOperational
  , BuiltinErrorToEvaluationError
  , builtinErrorToEvaluationError
  , throwBuiltinErrorWithCause
  ) where

import PlutusPrelude

import PlutusCore.Builtin.Result
import PlutusCore.Evaluation.ErrorWithCause
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Control.Monad.Except
import Data.Either.Extras
import Prettyprinter

-- | Errors which can occur during a run of an abstract machine.
data MachineError fun
  = -- | An attempt to reduce a not immediately reducible type instantiation.
    NonPolymorphicInstantiationMachineError
  | -- | An attempt to unwrap a not wrapped term.
    NonWrapUnwrappedMachineError
  | -- | An attempt to reduce a not immediately reducible application.
    NonFunctionalApplicationMachineError
  | -- | An attempt to evaluate an open term.
    OpenTermEvaluatedMachineError
  | -- | An attempt to compute a constant application resulted in 'UnliftingError'.
    UnliftingMachineError UnliftingError
  | -- | A builtin expected a term argument, but something else was received.
    BuiltinTermArgumentExpectedMachineError
  | -- | A builtin received a term argument when something else was expected
    UnexpectedBuiltinTermArgumentMachineError
  | -- | An attempt to scrutinize a non-constr.
    NonConstrScrutinizedMachineError
  | -- | An attempt to go into a non-existent case branch.
    MissingCaseBranchMachineError Word64
  | -- | A GHC exception was thrown.
    PanicMachineError String
  deriving stock (Show, Eq, Functor, Generic)
  deriving anyclass (NFData)

type EvaluationException structural operational =
  ErrorWithCause (EvaluationError structural operational)

{- Note [Ignoring context in OperationalError]
The 'OperationalError' error has a term argument, but 'splitStructuralOperational' just
discards this and returns 'EvaluationFailure'. This means that, for example, if we use the @plc@
command to execute a program containing a division by zero, @plc@ exits silently without reporting
that anything has gone wrong (but returning a non-zero exit code to the shell via 'exitFailure').
This is because 'OperationalError' is used in cases when a PLC program itself goes wrong
(see the Haddock of 'EvaluationError'). This is used to signal unsuccessful validation and so is
not regarded as a real error; in contrast structural errors are genuine errors and we report their
context if available.
-}

-- See the Haddock of 'EvaluationError' for what structural and operational errors are.
-- See Note [Ignoring context in OperationalError].
{-| Preserve the contents of an 'StructuralError' as a 'Left' and turn an
'OperationalError' into a @Right EvaluationFailure@ (thus erasing the content of the
error in the latter case). -}
splitStructuralOperational
  :: Either (EvaluationException structural operational term) a
  -> Either (ErrorWithCause structural term) (EvaluationResult a)
splitStructuralOperational (Right term) = Right $ EvaluationSuccess term
splitStructuralOperational (Left (ErrorWithCause evalErr cause)) = case evalErr of
  StructuralError err -> Left $ ErrorWithCause err cause
  OperationalError _ -> Right EvaluationFailure

{-| Throw on a 'StructuralError' and turn an 'OperationalError' into an
'EvaluationFailure' (thus erasing the content of the error in the latter case). -}
unsafeSplitStructuralOperational
  :: (PrettyPlc structural, PrettyPlc term, Typeable structural, Typeable term)
  => Either (EvaluationException structural operational term) a
  -> EvaluationResult a
unsafeSplitStructuralOperational = unsafeFromEither . splitStructuralOperational

instance
  (HasPrettyDefaults config ~ 'True, Pretty fun)
  => PrettyBy config (MachineError fun)
  where
  prettyBy _ NonPolymorphicInstantiationMachineError =
    "Attempted to instantiate a non-polymorphic term."
  prettyBy _ NonWrapUnwrappedMachineError =
    "Cannot unwrap a not wrapped term."
  prettyBy _ NonFunctionalApplicationMachineError =
    "Attempted to apply a non-function."
  prettyBy _ OpenTermEvaluatedMachineError =
    "Cannot evaluate an open term"
  prettyBy _ BuiltinTermArgumentExpectedMachineError =
    "A builtin expected a term argument, but something else was received"
  prettyBy _ UnexpectedBuiltinTermArgumentMachineError =
    "A builtin received a term argument when something else was expected"
  prettyBy _ (UnliftingMachineError unliftingError) =
    pretty unliftingError
  prettyBy _ NonConstrScrutinizedMachineError =
    "A non-constructor/non-builtin value was scrutinized in a case expression"
  prettyBy _ (MissingCaseBranchMachineError i) =
    "Case expression missing the branch required by the scrutinee tag:" <+> pretty i
  prettyBy _ (PanicMachineError err) =
    vcat
      [ "Panic: a GHC exception was thrown, please report this as a bug."
      , "The error: " <+> pretty err
      ]

class BuiltinErrorToEvaluationError structural operational where
  builtinErrorToEvaluationError :: BuiltinError -> EvaluationError structural operational

{-| Attach a @cause@ to a 'BuiltinError' and throw that.
Note that an evaluator might require the cause to be computed lazily for best performance on the
happy path, hence this function must not force its first argument.
TODO: wrap @cause@ in 'Lazy' once we have it. -}
throwBuiltinErrorWithCause
  :: ( MonadError (EvaluationException structural operational cause) m
     , BuiltinErrorToEvaluationError structural operational
     )
  => cause -> BuiltinError -> m void
throwBuiltinErrorWithCause cause e = throwErrorWithCause (builtinErrorToEvaluationError e) cause
{-# INLINE throwBuiltinErrorWithCause #-}
