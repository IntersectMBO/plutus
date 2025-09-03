-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module PlutusIR.Error
    ( Error (..)
    , PLC.TypeError
    , TypeErrorExt (..)
    , PLC.Normalized (..)
    ) where

import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC
import PlutusIR qualified as PIR
import PlutusPrelude

import Data.Text qualified as T
import Prettyprinter as PP

data TypeErrorExt uni ann =
      MalformedDataConstrResType
         !ann
         -- the expected constructor's type
         !(PLC.Type PLC.TyName uni ann)
    deriving stock (Show, Eq, Generic, Functor)
    deriving anyclass (NFData)

data Error uni fun a = CompilationError !a !T.Text -- ^ A generic compilation error.
                     | UnsupportedError !a !T.Text -- ^ An error relating specifically to an unsupported feature.
                     | OptionsError !T.Text -- ^ An error relating to compilation options.
                     | PLCError !(PLC.Error uni fun a) -- ^ An error from running some PLC function, lifted into this error type for convenience.
                     | PLCTypeError !(PLC.TypeError (PIR.Term PIR.TyName PIR.Name uni fun ()) uni fun a)
                     | PIRTypeError !(TypeErrorExt uni a)
                     deriving stock (Functor)

-- Pretty-printing
------------------

instance (PLC.PrettyUni uni, Pretty ann) =>
        PrettyBy PLC.PrettyConfigPlc (TypeErrorExt uni ann) where
    prettyBy config (MalformedDataConstrResType ann expType) =
        vsep ["The result-type of a dataconstructor is malformed at location" <+> PP.pretty ann
             , "The expected result-type is:" <+> prettyBy config expType]

-- show via pretty, for printing as SomeExceptions
instance (PLC.PrettyUni uni, Pretty fun, Pretty ann) => Show (Error uni fun ann) where
    show = show . PP.pretty

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1732): we get rid of this
-- when our TestLib stops using rethrow
deriving anyclass instance
    (PLC.ThrowableBuiltins uni fun, PP.Pretty ann, Typeable ann) => Exception (Error uni fun ann)

instance (PLC.PrettyUni uni, Pretty fun, Pretty ann) => Pretty (Error uni fun ann) where
    pretty = PLC.prettyPlcClassic


instance (PLC.PrettyUni uni, Pretty fun, Pretty ann) =>
        PrettyBy PLC.PrettyConfigPlc (Error uni fun ann) where
     prettyBy config = \case
        CompilationError x e -> "Error during compilation:" <+> PP.pretty e <> "(" <> PP.pretty x <> ")"
        UnsupportedError x e -> "Unsupported construct:" <+> PP.pretty e <+> "(" <> PP.pretty x <> ")"
        OptionsError e       -> "Compiler options error:" <+> PP.pretty e
        PLCError e           -> PP.vsep [ "Error from the PLC compiler:", PLC.prettyBy config e ]
        PLCTypeError e       -> PP.vsep ["Error during PIR typechecking:" , PLC.prettyBy config e ]
        PIRTypeError e       -> PP.vsep ["Error during PIR typechecking:" , PLC.prettyBy config e ]
