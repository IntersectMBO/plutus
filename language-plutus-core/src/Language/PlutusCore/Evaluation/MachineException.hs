-- | The exceptions that an abstract machine can throw.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Evaluation.MachineException
    ( MachineError(..)
    , MachineException(..)
    ) where

import           Language.PlutusCore.Constant.Apply
import           Language.PlutusCore.Name
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Errors which can occur during a run of an abstract machine.
data MachineError
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

-- | The type of exceptions an abstract machine can throw.
data MachineException = MachineException
    { _machineExceptionError :: MachineError         -- ^ An error.
    , _machineExceptionCause :: Term TyName Name ()  -- ^ A 'Term' that caused the error.
    }

instance PrettyCfg MachineError where
    prettyCfg _   NonPrimitiveInstantiationMachineError =
        "Cannot reduce a not immediately reducible type instantiation."
    prettyCfg _   NonWrapUnwrappedMachineError          =
        "Cannot unwrap a not wrapped term."
    prettyCfg _   NonPrimitiveApplicationMachineError   =
        "Cannot reduce a not immediately reducible application."
    prettyCfg _   OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term."
    prettyCfg cfg (ConstAppMachineError constAppError)  =
        prettyCfg cfg constAppError

instance Show MachineException where
    show (MachineException err cause) = fold
        [ "An abstract machine failed: " , prettyCfgString err, "\n"
        , "Caused by: ", prettyCfgString cause
        ]

instance Exception MachineException
