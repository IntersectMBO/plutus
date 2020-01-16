-- | The exceptions that an abstract machine can throw.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.Exception
    ( MachineError (..)
    , MachineException (..)
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty

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
    | OutOfExError
      -- ^ An attempt to continue evaluation without sufficient Ex
    | OtherMachineError err
    deriving (Eq)

-- | The type of exceptions an abstract machine can throw.
data MachineException err = MachineException
    { _machineExceptionError :: MachineError err     -- ^ An error.
    , _machineExceptionCause :: Term TyName Name ()  -- ^ A 'Term' that caused the error.
    } deriving (Eq)

instance ( PrettyBy config (Term TyName Name ())
         , Pretty err
         ) => PrettyBy config (MachineError err) where
    prettyBy _      NonPrimitiveInstantiationMachineError =
        "Cannot reduce a not immediately reducible type instantiation."
    prettyBy _      NonWrapUnwrappedMachineError          =
        "Cannot unwrap a not wrapped term."
    prettyBy _      NonPrimitiveApplicationMachineError   =
        "Cannot reduce a not immediately reducible application."
    prettyBy _      OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term."
    prettyBy _      OutOfExError         =
        "Cannot continue without Ex."
    prettyBy config (ConstAppMachineError constAppError)  =
        prettyBy config constAppError
    prettyBy _      (OtherMachineError err)               =
        pretty err

instance Pretty err => Show (MachineException err) where
    show (MachineException err cause) = fold
        [ "An abstract machine failed: ", docString $ prettyPlcReadableDebug err, "\n"
        , "Caused by: ", docString $ prettyPlcReadableDebug cause
        ]

instance (Pretty err, Typeable err) => Exception (MachineException err)
