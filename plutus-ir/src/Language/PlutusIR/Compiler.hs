{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    compileProgram,
    Compiling,
    Error (..),
    AsError (..),
    Provenance (..)) where

import           Language.PlutusIR

import           Language.PlutusIR.Compiler.Error
import qualified Language.PlutusIR.Compiler.Let              as Let
import           Language.PlutusIR.Compiler.Lower
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types
import           Language.PlutusIR.Transform.Rename          ()
import           Language.PlutusIR.Transform.ThunkRecursions

import qualified Language.PlutusCore                         as PLC

import           Control.Monad

-- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m e a => Term TyName Name a -> m (PLCTerm a)
compileTerm =
    lowerTerm
    <=< Let.compileLets Let.NonRecTerms
    <=< Let.compileLets Let.RecTerms
    <=< Let.compileLets Let.Types
    <=< thunkRecursionsTerm . original

-- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram :: Compiling m e a => Program TyName Name a -> m (PLC.Program TyName Name (Provenance a))
compileProgram (Program a t) = PLC.Program (Original a) (PLC.defaultVersion (Original a)) <$> compileTerm t
