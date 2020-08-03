{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    compileToReadable,
    compileReadableToPlc,
    Compiling,
    Error (..),
    AsError (..),
    Provenance (..),
    noProvenance,
    CompilationOpts,
    coOptimize,
    defaultCompilationOpts,
    CompilationCtx,
    ccOpts,
    ccEnclosing,
    ccBuiltinMeanings,
    defaultCompilationCtx) where

import           Language.PlutusIR

import           Language.PlutusIR.Compiler.Error
import qualified Language.PlutusIR.Compiler.Let              as Let
import           Language.PlutusIR.Compiler.Lower
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.Optimizer.DeadCode        as DeadCode
import qualified Language.PlutusIR.Transform.LetFloat        as LetFloat
import qualified Language.PlutusIR.Transform.NonStrict       as NonStrict
import           Language.PlutusIR.Transform.Rename          ()
import qualified Language.PlutusIR.Transform.ThunkRecursions as ThunkRec

import qualified Language.PlutusCore                         as PLC

import           Control.Monad
import           Control.Monad.Reader

-- | Perform some simplification of a 'Term'.
simplifyTerm :: Compiling m e uni a => Term TyName Name uni b -> m (Term TyName Name uni b)
simplifyTerm = runIfOpts deadCode
    where
        deadCode t = do
            means <- asks _ccBuiltinMeanings
            pure $ DeadCode.removeDeadBindings means t

-- | Perform floating/merging of lets in a 'Term' to their nearest lambda/Lambda/letStrictNonValue.
-- Note: It assumes globally unique names
floatTerm :: (Compiling m e uni a, Semigroup b) => Term TyName Name uni b -> m (Term TyName Name uni b)
floatTerm = runIfOpts letFloat
    where
        letFloat t = do
            means <- asks _ccBuiltinMeanings
            pure $ LetFloat.floatTerm means t

-- | The 1st half of the PIR compiler pipeline up to floating/merging the lets.
-- We stop momentarily here to give a chance to the tx-plugin
-- to dump a "readable" version of pir (i.e. floated).
compileToReadable :: Compiling m e uni a
                  => Term TyName Name uni a -> m (Term TyName Name uni (Provenance a))
compileToReadable =
    (pure . original)
    >=> simplifyTerm
    >=> (pure . ThunkRec.thunkRecursions)
    -- We need globally unique names for floating and compiling non-strict bindings away
    >=> PLC.rename
    >=> floatTerm

-- | The 2nd half of the PIR compiler pipeline.
-- Compiles a 'Term' into a PLC Term, by removing/translating step-by-step the PIR's language construsts to PLC.
-- Note: the result *does* have globally unique names.
compileReadableToPlc :: Compiling m e uni a => Term TyName Name uni (Provenance a) -> m (PLCTerm uni a)
compileReadableToPlc =
    NonStrict.compileNonStrictBindings
    >=> Let.compileLets Let.Types
    >=> Let.compileLets Let.RecTerms
    -- We introduce some non-recursive let bindings while eliminating recursive let-bindings, so we
    -- can eliminate any of them which are unused here.
    >=> simplifyTerm
    >=> Let.compileLets Let.NonRecTerms
    >=> lowerTerm


--- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m e uni a => Term TyName Name uni a -> m (PLCTerm uni a)
compileTerm = compileToReadable >=> compileReadableToPlc
