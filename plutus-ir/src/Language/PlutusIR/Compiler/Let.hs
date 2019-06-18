{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR let terms.
module Language.PlutusIR.Compiler.Let (compileLets, LetKind(..)) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.MkPir               as PIR

import           Control.Monad
import           Control.Monad.Error.Lens

import           Control.Lens                          hiding (Strict)

import           Data.List

data LetKind = RecTerms | NonRecTerms | Types

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e a => LetKind -> PIRTerm a -> m (PIRTerm a)
compileLets kind = transformMOf termSubterms (compileLet kind)

compileLet :: Compiling m e a => LetKind -> PIRTerm a -> m (PIRTerm a)
compileLet kind = \case
    Let p r bs body -> withEnclosing (const $ LetBinding r p) $ case r of
            NonRec -> foldM (compileNonRecBinding kind) body bs
            Rec    -> compileRecBindings kind body bs
    x -> pure x

compileRecBindings :: Compiling m e a => LetKind -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecBindings kind body bs
    | null typeBinds = compileRecTermBindings kind body termBinds
    | null termBinds = compileRecTypeBindings kind body typeBinds
    | otherwise      = getEnclosing >>= \p -> throwing _Error $ CompilationError p "Mixed term and type bindings in recursive let"
    where
        (termBinds, typeBinds) = partition (\case { TermBind {} -> True ; _ -> False; }) bs

compileRecTermBindings :: Compiling m e a => LetKind -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTermBindings RecTerms body bs = do
    binds <- forM bs $ \case
        TermBind _ Strict vd rhs -> pure $ PIR.Def vd rhs
        _ -> getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
    compileRecTerms body binds
compileRecTermBindings _ body bs = getEnclosing >>= \p -> pure $ Let p Rec bs body

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
