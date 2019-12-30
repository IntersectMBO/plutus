-- | The exceptions that an abstract machine can throw.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Evaluation.MachineException
    ( MachineError (..)
    , MachineException (..)
    ) where

import           Language.PlutusCore.Erasure.Untyped.Constant
import           Language.PlutusCore.Erasure.Untyped.Instance.Pretty ()
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           PlutusPrelude

-- | Errors which can occur during a run of an abstract machine.
data MachineError err
    = NonPrimitiveInstantiationMachineError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonPrimitiveApplicationMachineError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedMachineError
      -- ^ An attempt to evaluate an open term.
    | ConstAppMachineError ConstAppError
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.
    | OtherMachineError err
    deriving (Eq)

-- | The type of exceptions an abstract machine can throw.
data MachineException err = MachineException
    { _machineExceptionError :: MachineError err     -- ^ An error.
    , _machineExceptionCause :: Term Name ()  -- ^ A 'Term' that caused the error.
    } deriving (Eq)

instance Pretty err => PrettyBy config (MachineError err) where
    prettyBy _      NonPrimitiveInstantiationMachineError =
        "Cannot reduce a not immediately reducible type instantiation."
    prettyBy _      NonPrimitiveApplicationMachineError   =
        "Cannot reduce a not immediately reducible application."
    prettyBy _      OpenTermEvaluatedMachineError         =
        "Cannot evaluate an open term."
    prettyBy _ (ConstAppMachineError _)  =
         "constAppError" -- prettyBy config constAppError
    prettyBy _      (OtherMachineError err)               =
        pretty err

instance Pretty err => Show (MachineException err) where
    show (MachineException err cause) = fold
        [ "An abstract machine failed: ", docString $ prettyPlcReadableDebug err, "\n"
        , "Caused by: ", docString $ prettyPlcReadableDebug cause
        ]

instance (Pretty err, Typeable err) => Exception (MachineException err)
