{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.PlutusIR.Compiler (
    compileTerm,
    compileToReadable,
    compileToReadable',
    compileReadableToPlc,
    compileReadableToPlc',
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
    ccTypeCheckConfig,
    PirTCConfig(..),
    AllowEscape(..),
    toDefaultCompilationCtx,
    Pass(..),
    CompilationTrace(..)) where

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
simplifyTerm = runIfOpts $ pure . fst . Inline.inline . DeadCode.removeDeadBindings

simplifyTerm' :: Compiling m e uni fun a => PIRTerm uni fun b -> m (PIRTerm uni fun b, [PassRes uni fun b])
simplifyTerm' t = runIfOpts (\(t',_) ->  -- ugly workaround to get types of runIfOpts to line up
  let t1 = DeadCode.removeDeadBindings t'
      (t2, eliminated) = Inline.inline t1
      ctrace = [ (PassDeadCode          , t1)
               , (PassInline eliminated , t2)
               ]
  in pure (t2, ctrace)) (t, [])

-- | Perform floating/merging of lets in a 'Term' to their nearest lambda/Lambda/letStrictNonValue.
-- Note: It assumes globally unique names
floatTerm :: (Compiling m e uni fun a, Semigroup b) => Term TyName Name uni fun b -> m (Term TyName Name uni fun b)
floatTerm = runIfOpts $ pure . LetFloat.floatTerm

-- | Typecheck a PIR Term iff the context demands it.
-- Note: assumes globally unique names
typeCheckTerm :: Compiling m e uni fun b => Term TyName Name uni fun (Provenance b) -> m ()
typeCheckTerm t = do
    mtcconfig <- asks _ccTypeCheckConfig
    case mtcconfig of
        Just tcconfig -> void . runTypeCheckM tcconfig $ inferTypeM t
        Nothing       -> pure ()

-- | The 1st half of the PIR compiler pipeline up to floating/merging the lets.
-- We stop momentarily here to give a chance to the tx-plugin
-- to dump a "readable" version of pir (i.e. floated).
compileToReadable :: Compiling m e uni fun a
                  => Term TyName Name uni fun a
                  -> m (Term TyName Name uni fun (Provenance a))
compileToReadable =
    (pure . original)
    -- We need globally unique names for typechecking, floating, and compiling non-strict bindings
    >=> PLC.rename
    >=> through typeCheckTerm
    >=> simplifyTerm
    >=> (pure . ThunkRec.thunkRecursions)
    >=> floatTerm

-- to dump a "readable" version of pir (i.e. floated).
compileToReadable' :: Compiling m e uni fun a
                  => Term TyName Name uni fun a
                  -> m (Term TyName Name uni fun (Provenance a), CompilationTrace uni fun a)
compileToReadable' x0 = do
    x1 <- (pure . original) x0
    -- We need globally unique names for typechecking, floating, and compiling non-strict bindings
    x2 <- PLC.rename x1
    x3 <- through typeCheckTerm x2
    (x4, simplifyTrace) <- simplifyTerm' x3
    x5 <- (pure . ThunkRec.thunkRecursions) x4
    x6 <- floatTerm x5
    let ctrace = CompilationTrace x1 $
          [ (PassRename    , x2)
          , (PassTypeCheck , x3)
          ]
          ++ simplifyTrace ++
          [ (PassThunkRec  , x5)
          , (PassFloatTerm , x6)
          ]

    return (x6, ctrace)

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

compileReadableToPlc' :: Compiling m e uni fun a => Term TyName Name uni fun (Provenance a) -> m (PLCTerm uni fun a, [PassRes uni fun a])
compileReadableToPlc' x0 = do
    x1 <- NonStrict.compileNonStrictBindings x0
    x2 <- Let.compileLets Let.Types x1
    x3 <- Let.compileLets Let.RecTerms x2
    -- We introduce some non-recursive let bindings while eliminating recursive let-bindings, so we
    -- can eliminate any of them which are unused here.
    (x4, simplifyTrace) <- simplifyTerm' x3
    x5 <- Let.compileLets Let.NonRecTerms x4
    x6 <- lowerTerm x5
    let ctrace =
          [ (PassLetNonStrict, x1)
          , (PassLetTypes , x2)
          , (PassLetRec   , x3)
          ] ++ simplifyTrace ++
          [ (PassLetNonRec, x5)
          ]
    return (x6, ctrace)

--- | Compile a 'Term' into a PLC Term. Note: the result *does* have globally unique names.
compileTerm :: Compiling m e uni fun a
            => Term TyName Name uni fun a -> m (PLCTerm uni fun a)
compileTerm = compileToReadable >=> compileReadableToPlc


-- | Each pass, including any additional information about
-- what the pass did
data Pass
  = PassRename
  | PassTypeCheck
  | PassInline [Name] -- The Names that were unconditionally inlined and thus eliminated
  | PassDeadCode
  | PassThunkRec
  | PassFloatTerm
  | PassLetNonStrict
  | PassLetTypes
  | PassLetRec
  | PassLetNonRec
  deriving (Show)

type PassRes uni fun a = (Pass, PIRTerm uni fun a)

data CompilationTrace uni fun a =
  CompilationTrace
    (PIRTerm uni fun a)
    [PassRes uni fun a]
