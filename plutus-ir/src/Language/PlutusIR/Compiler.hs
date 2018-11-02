{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    Compiling,
    CompError (..),
    runCompiling) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Error
import qualified Language.PlutusIR.Compiler.Term  as Term
import           Language.PlutusIR.Compiler.Types

import qualified Language.PlutusCore              as PLC

import           Control.Monad

-- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m => Term TyName Name () -> m (PLC.Term TyName Name ())
compileTerm = PLC.rename <=< Term.compileTerm
