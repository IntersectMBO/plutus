{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    compileProgram,
    simplifyTerm,
    Compiling,
    Error (..),
    AsError (..),
    Provenance (..),
    CompilationOpts,
    coOptimize,
    defaultCompilationOpts,
    CompilationCtx,
    ccOpts,
    ccEnclosing,
    defaultCompilationCtx) where

import           Language.PlutusIR

import           Language.PlutusIR.Compiler.Error
import qualified Language.PlutusIR.Compiler.Let              as Let
import           Language.PlutusIR.Compiler.Lower
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.Optimizer.DeadCode        as DeadCode
import           Language.PlutusIR.Transform.Rename          ()
import qualified Language.PlutusIR.Transform.ThunkRecursions as ThunkRec

import qualified Language.PlutusCore                         as PLC

import           Control.Monad
import           Control.Monad.Reader

-- | Perform some simplification of a 'Term'.
simplifyTerm :: MonadReader (CompilationCtx a) m => Term TyName Name b -> m (Term TyName Name b)
simplifyTerm = runIfOpts (pure . DeadCode.removeDeadBindings)

-- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m e a => Term TyName Name a -> m (PLCTerm a)
compileTerm =
    (pure . original)
    >=> simplifyTerm
    >=> ThunkRec.thunkRecursionsTerm
    >=> Let.compileLets Let.Types
    >=> Let.compileLets Let.RecTerms
    -- We introduce some non-recursive let bindings while eliminating recursive let-bindings, so we
    -- can eliminate any of them which are unused here.
    >=> simplifyTerm
    >=> Let.compileLets Let.NonRecTerms
    >=> lowerTerm

-- | Compile a 'Program' into a PLC Program. Note: the result *does* have globally unique names.
compileProgram :: Compiling m e a => Program TyName Name a -> m (PLC.Program TyName Name (Provenance a))
compileProgram (Program a t) = PLC.Program (Original a) (PLC.defaultVersion (Original a)) <$> compileTerm t
