{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module Language.PlutusIR.Compiler.Error (CompError (..)) where

import qualified Language.PlutusCore        as PLC
import qualified Language.PlutusCore.Pretty as PLC

import qualified Data.Text                  as T
import qualified Data.Text.Prettyprint.Doc  as PP

data CompError a = CompilationError T.Text -- ^ A generic compilation error.
                 | UnsupportedError T.Text -- ^ An error relating specifically to an unsupported feature.
                 | PLCError (PLC.Error a) -- ^ An error from running some PLC function, lifted into this error type for convenience.

instance PP.Pretty a => PLC.PrettyBy PLC.PrettyConfigPlc (CompError a) where
    prettyBy config = \case
        CompilationError e -> "Error during compilation:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported:" PP.<+> PP.pretty e
        PLCError e -> PLC.prettyBy config e
