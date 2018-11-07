{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    compileProgram,
    Compiling,
    CompError (..),
    Provenance (..)) where

import           Language.PlutusIR

import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import qualified Language.PlutusIR.Compiler.Term       as Term
import           Language.PlutusIR.Compiler.Types

import qualified Language.PlutusCore                   as PLC

import           Control.Monad

-- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m a => Term TyName Name a -> m (PLCTerm a)
compileTerm = (PLC.rename <=< Term.compileTerm) . original

-- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram :: Compiling m a => Program TyName Name a -> m (PLC.Program TyName Name (Provenance a))
compileProgram (Program a t) = PLC.Program (Original a) (PLC.defaultVersion (Original a)) <$> compileTerm t
