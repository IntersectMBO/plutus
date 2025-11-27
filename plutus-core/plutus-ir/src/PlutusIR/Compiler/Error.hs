-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusIR.Compiler.Error (Error (..)) where

import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC

import Control.Exception

import Data.Text qualified as T
import Data.Typeable
import Prettyprinter ((<+>))
import Prettyprinter qualified as PP

data Error uni fun a
  = -- | A generic compilation error.
    CompilationError !a !T.Text
  | -- | An error relating specifically to an unsupported feature.
    UnsupportedError !a !T.Text
  | {-| An error from running some PLC function, lifted into
    this error type for convenience. -}
    PLCError !(PLC.Error uni fun a)

instance (PLC.PrettyUni uni, PP.Pretty fun, PP.Pretty ann) => Show (Error uni fun ann) where
  show = show . PLC.prettyPlcClassicSimple

instance
  (PLC.PrettyUni uni, PP.Pretty fun, PP.Pretty ann)
  => PLC.PrettyBy PLC.PrettyConfigPlc (Error uni fun ann)
  where
  prettyBy config = \case
    CompilationError x e -> "Error during compilation:" <+> PP.pretty e <> "(" <> PP.pretty x <> ")"
    UnsupportedError x e -> "Unsupported construct:" <+> PP.pretty e <+> "(" <> PP.pretty x <> ")"
    PLCError e -> PP.vsep ["Error from the PLC compiler:", PLC.prettyBy config e]

deriving anyclass instance
  (PLC.ThrowableBuiltins uni fun, PP.Pretty ann, Typeable ann) => Exception (Error uni fun ann)
