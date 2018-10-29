{-# LANGUAGE FlexibleContexts  #-}
module Language.PlutusIR.Compiler.Term (compileTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Types

import qualified Language.PlutusCore                 as PLC

compileTerm :: Compiling m => Term TyName Name () -> m (PLC.Term TyName Name ())
