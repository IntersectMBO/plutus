{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler.Types where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Error

import           Control.Monad.Except

import qualified Language.PlutusCore.MkPlc        as PLC
import           Language.PlutusCore.Quote

type Compiling m = (Monad m, MonadError (CompError ()) m, MonadQuote m)

runCompiling :: QuoteT (Except (CompError())) a -> Either (CompError ()) a
runCompiling = runExcept . runQuoteT

type TermDef tyname name a = PLC.Def (PLC.VarDecl tyname name a) (Term tyname name a)
