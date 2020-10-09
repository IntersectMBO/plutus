{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.PlutusIR.Compiler (
    compileTerm,
    compileToReadable,
    compileReadableToPlc,
    Compiling,
    Error (..),
    AsError (..),
    AsTypeError (..),
    AsTypeErrorExt (..),
    Provenance (..),
    noProvenance,
    CompilationOpts,
    coOptimize,
    defaultCompilationOpts,
    CompilationCtx,
    ccOpts,
    ccEnclosing,
    ccBuiltinMeanings,
    ccTypeCheckConfig,
    PirTCConfig(..),
    AllowEscape(..),
    defaultCompilationCtx) where

import           Language.PlutusIR

import qualified Language.PlutusIR.Compiler.Let              as Let
import           Language.PlutusIR.Compiler.Lower
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types
import           Language.PlutusIR.Error
import qualified Language.PlutusIR.Optimizer.DeadCode        as DeadCode
import qualified Language.PlutusIR.Transform.Inline          as Inline
import qualified Language.PlutusIR.Transform.LetFloat        as LetFloat
import qualified Language.PlutusIR.Transform.NonStrict       as NonStrict
import           Language.PlutusIR.Transform.Rename          ()
import qualified Language.PlutusIR.Transform.ThunkRecursions as ThunkRec
import           Language.PlutusIR.TypeCheck.Internal

import qualified Language.PlutusCore                         as PLC

import           Control.Monad
import           Control.Monad.Reader
import           PlutusPrelude

-- | Perform some simplification of a 'Term'.
simplifyTerm :: Compiling m e uni fun a => Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
simplifyTerm = runIfOpts $ \t -> do
    means <- asks _ccBuiltinMeanings
    pure $ Inline.inline means $ DeadCode.removeDeadBindings means t

-- | Perform floating/merging of lets in a 'Term' to their nearest lambda/Lambda/letStrictNonValue.
-- Note: It assumes globally unique names
floatTerm :: (Compiling m e uni fun a, Semigroup b) => Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
floatTerm = runIfOpts letFloat
    where
        letFloat t = do
            means <- asks _ccBuiltinMeanings
            pure $ LetFloat.floatTerm means t

-- | Perform typechecking of a PIR Term.
-- Note: assumes globally unique names
typeCheckTerm :: Compiling m e uni fun b => Term TyName Name uni fun (Provenance b) -> m ()
typeCheckTerm t = do
    tcconfig <- asks _ccTypeCheckConfig
    void . runTypeCheckM tcconfig $ inferTypeM t

-- | The 1st half of the PIR compiler pipeline up to floating/merging the lets.
-- We stop momentarily here to give a chance to the tx-plugin
-- to dump a "readable" version of pir (i.e. floated).
compileToReadable :: Compiling m e uni fun a
                  => Bool
                  -> Term TyName Name uni fun a
                  -> m (Term TyName Name uni fun (Provenance a))
compileToReadable doTypecheck =
    (pure . original)
    -- We need globally unique names for typechecking, floating, and compiling non-strict bindings
    >=> PLC.rename
    >=> through (when doTypecheck . typeCheckTerm)
    >=> simplifyTerm
    >=> (pure . ThunkRec.thunkRecursions)
    >=> floatTerm

-- | The 2nd half of the PIR compiler pipeline.
-- Compiles a 'Term' into a PLC Term, by removing/translating step-by-step the PIR's language construsts to PLC.
-- Note: the result *does* have globally unique names.
compileReadableToPlc :: Compiling m e uni fun a => Term TyName Name uni fun (Provenance a) -> m (PLCTerm uni fun a)
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
compileTerm :: Compiling m e uni fun a
            => Bool -- ^ flag to run PIR-typecheking or not (for debuggin purposes)
            -> Term TyName Name uni fun a -> m (PLCTerm uni fun a)
compileTerm doTypecheck  = compileToReadable doTypecheck >=> compileReadableToPlc
