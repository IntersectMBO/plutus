{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR let terms.
module Language.PlutusIR.Compiler.Let (compileLets, LetKind(..)) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Definitions
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.MkPir                as PIR

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Trans

import           Control.Lens                           hiding (Strict)

import           Data.List

{- Note [Extra definitions while compiling let-bindings]
The let-compiling passes can generate some additional definitions, so we use the
support from 'Definitions' to ease this.

Specifically, only the recursive term pass should do this (it helps to share fixpoint combinators).
So putting in the definitions should mostly be a no-op, and we'll get errors if it's not.
It would be more elegant to somehow indicate that only one of the let-compiling passes needs
this, but this does the job.
Also we should pull out more stuff (e.g. see 'NonStrict' which uses unit).
-}

{- Note [Right-associative compilation of let-bindings for linear scoping]

The 'foldM' function for lists is left-associative, but we need right-associative for our case, i.e.
every right let must be wrapped/scoped by its left let

An pseudocode PIR example:
let b1 = rhs1;
    b2 = rhs2  (b1 is visible in rhs2);
in ...

must be treated the same as let b1 = rhs in (let b2 = rhs2 in ... )

Since there is no 'foldrM' in the stdlib, so we first reverse the bindings list,
and then apply the left-associative 'foldM' on them,
which yields the same results as doing a right-associative fold.
-}

data LetKind = RecTerms | NonRecTerms | Types

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e a => LetKind -> PIRTerm a -> m (PIRTerm a)
compileLets kind t = getEnclosing >>= \p ->
    -- See Note [Extra definitions while compiling let-bindings]
    runDefT p $ transformMOf termSubterms (compileLet kind) t

compileLet :: Compiling m e a => LetKind -> PIRTerm a -> DefT SharedName (Provenance a) m (PIRTerm a)
compileLet kind = \case
    Let p r bs body -> withEnclosing (const $ LetBinding r p) $ case r of
            -- See Note [Right-associative compilation of let-bindings for linear scoping]
            NonRec -> lift $ foldM (compileNonRecBinding kind) body (reverse bs)
            Rec    -> compileRecBindings kind body bs
    x -> pure x

compileRecBindings
    :: Compiling m e a
    => LetKind
    -> PIRTerm a
    -> [Binding TyName Name (Provenance a)]
    -> DefT SharedName (Provenance a) m (PIRTerm a)
compileRecBindings kind body bs
    | null typeBinds = compileRecTermBindings kind body termBinds
    | null termBinds = lift $ compileRecTypeBindings kind body typeBinds
    | otherwise      = lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Mixed term and type bindings in recursive let"
    where
        (termBinds, typeBinds) = partition (\case { TermBind {} -> True ; _ -> False; }) bs

compileRecTermBindings
    :: Compiling m e a
    => LetKind
    -> PIRTerm a
    -> [Binding TyName Name (Provenance a)]
    -> DefT SharedName (Provenance a) m (PIRTerm a)
compileRecTermBindings RecTerms body bs = do
    binds <- forM bs $ \case
        TermBind _ Strict vd rhs -> pure $ PIR.Def vd rhs
        _ -> lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
    compileRecTerms body binds
compileRecTermBindings _ body bs = lift $ getEnclosing >>= \p -> pure $ Let p Rec bs body

compileRecTypeBindings :: Compiling m e a => LetKind -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTypeBindings Types body bs = do
    binds <- forM bs $ \case
        DatatypeBind _ d -> pure d
        _ -> getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: term or type binding in datatype binding group"
    compileRecDatatypes body binds
compileRecTypeBindings _ body bs = getEnclosing >>= \p -> pure $ Let p Rec bs body

compileNonRecBinding :: Compiling m e a => LetKind -> PIRTerm a -> Binding TyName Name (Provenance a) -> m (PIRTerm a)
compileNonRecBinding NonRecTerms body (TermBind x Strict d rhs) = withEnclosing (const $ TermBinding (varDeclNameString d) x) $
   PIR.mkImmediateLamAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (TypeBind x d rhs) = withEnclosing (const $ TypeBinding (tyVarDeclNameString d) x) $
   PIR.mkImmediateTyAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (DatatypeBind x d) = withEnclosing (const $ TypeBinding (datatypeNameString d) x) $
   compileDatatype NonRec body d
compileNonRecBinding _ body b = getEnclosing >>= \p -> pure $ Let p NonRec [b] body
