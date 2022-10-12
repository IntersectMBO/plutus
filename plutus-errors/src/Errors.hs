-- editorconfig-checker-disable-file
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- | The catalogue of all Plutus errors, obsolete or not.
module Errors (allErrors) where

import ErrorCode
import Language.Haskell.TH as TH

import PlutusCore.DeBruijn qualified as PLC
import PlutusCore.Error qualified as PLC
import PlutusCore.Evaluation.Machine.Exception qualified as PLC
import PlutusIR.Error qualified as PIR
import PlutusTx.Code qualified as PTX
import PlutusTx.Compiler.Error qualified as PTX
import PlutusTx.Lift qualified as PTX
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as PLC

{- | A collection of error instances which are obsolete, together with their error codes bundled to one instance.
See plutus-errors/README.md
-}
{-# WARNING ObsoleteErrors "These errors and their error codes *should* not be thrown by any plutus code anymore" #-}
data ObsoleteErrors =
    ReservedErrorCode
  | EmptyBuiltinArityMachineError
  -- ^ an old error when we were checking arities of builtins during evaluation

    -- append here the obsolete errors

instance HasErrorCode ObsoleteErrors where
    errorCode ReservedErrorCode {}             = ErrorCode 0
    errorCode EmptyBuiltinArityMachineError {} = ErrorCode 34
    -- append here the corresponding obsolete error codes

-- | All errors among the whole Plutus project. This includes both existing and obsolete errors.
-- Note: the order of adding to this list does not matter, except for haddock looks.
allErrors :: [TH.Name]
allErrors =
   [ 'ReservedErrorCode
   , 'PIR.MalformedDataConstrResType
   , 'PIR.CompilationError
   , 'PIR.UnsupportedError
   , 'PLC.UnknownBuiltinType
   , 'PLC.BuiltinTypeNotAStar
   , 'PLC.UnknownBuiltinFunction
   , 'PLC.InvalidBuiltinConstant
   , 'PLC.MultiplyDefined
   , 'PLC.IncoherentUsage
   , 'PLC.BadType
   , 'PLC.BadTerm
   , 'PLC.KindMismatch
   , 'PLC.TypeMismatch
   , 'PLC.UnknownBuiltinFunctionE
   , 'PLC.TyNameMismatch
   , 'PLC.NameMismatch
   , 'PLC.FreeTypeVariableE
   , 'PLC.FreeVariableE
   , 'PLC.FreeVariable
   , 'PLC.FreeUnique
   , 'PLC.FreeIndex
   , 'PLC.NonPolymorphicInstantiationMachineError
   , 'PLC.NonWrapUnwrappedMachineError
   , 'PLC.NonFunctionalApplicationMachineError
   , 'PLC.OpenTermEvaluatedMachineError
   , 'PLC.UnliftingErrorE
   , 'PLC.BuiltinTermArgumentExpectedMachineError
   , 'PLC.UnexpectedBuiltinTermArgumentMachineError
   , 'PLC.CekOutOfExError
   , 'PLC.CekEvaluationFailure
   , 'PLC.ParseErrorB
   , 'PTX.ImpossibleDeserialisationFailure
   , 'PTX.CompilationError
   , 'PTX.UnsupportedError
   , 'PTX.FreeVariableError
   , 'PTX.InvalidMarkerError
   , 'PTX.CoreNameLookupError
   , 'PTX.UnsupportedLiftType
   , 'PTX.UnsupportedLiftKind
   , 'PTX.UserLiftError
   , 'PTX.LiftMissingDataCons
   , 'PTX.LiftMissingVar
   ]
