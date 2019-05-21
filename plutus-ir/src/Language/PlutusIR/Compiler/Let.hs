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

import           Data.List

data LetKind = RecTerms | NonRecTerms | Types

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e a => LetKind -> PIRTerm a -> m (PIRTerm a)
compileLets kind = \case
    Let p r bs body -> withEnclosing (const $ LetBinding r p) $ do
        body' <- compileLets kind body
        bs' <- traverse (compileInBinding kind) bs
        case r of
            NonRec -> foldM (compileNonRecBinding kind) body' bs'
            Rec    -> compileRecBindings kind body' bs'
    Var x n -> pure $ Var x n
    TyAbs x n k t -> TyAbs x n k <$> compileLets kind t
    LamAbs x n ty t -> LamAbs x n ty <$> compileLets kind t
    Apply x t1 t2 -> Apply x <$> compileLets kind t1 <*> compileLets kind t2
    Constant x c -> pure $ Constant x c
    Builtin x bi -> pure $ Builtin x bi
    TyInst x t ty -> TyInst x <$> compileLets kind t <*> pure ty
    Error x ty -> pure $ Error x ty
    IWrap x tn ty t -> IWrap x tn ty <$> compileLets kind t
    Unwrap x t -> Unwrap x <$> compileLets kind t

compileInBinding
    :: Compiling m e a
    => LetKind
    -> Binding TyName Name (Provenance a)
    -> m (Binding TyName Name (Provenance a))
compileInBinding kind b = case b of
    TermBind x d rhs -> TermBind x d <$> compileLets kind rhs
    _                -> pure b

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
        TermBind _ vd rhs -> pure $ PIR.Def vd rhs
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
compileNonRecBinding NonRecTerms body (TermBind x d rhs) = withEnclosing (const $ TermBinding (varDeclNameString d) x) $
   PIR.mkTermLet <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (TypeBind x d rhs) = withEnclosing (const $ TypeBinding (tyVarDeclNameString d) x) $
   PIR.mkTypeLet <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (DatatypeBind x d) = withEnclosing (const $ TypeBinding (datatypeNameString d) x) $
   compileDatatype NonRec body d
compileNonRecBinding _ body b = getEnclosing >>= \p -> pure $ Let p NonRec [b] body
