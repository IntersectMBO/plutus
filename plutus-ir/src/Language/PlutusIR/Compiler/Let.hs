{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR let terms.
module Language.PlutusIR.Compiler.Let (compileLets) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types
import qualified Language.PlutusIR.MkPir as PIR

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Reader

import           Data.List

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e a => PIRTerm a -> m (PIRTerm a)
compileLets = \case
    Let p r bs body -> local (const $ LetBinding r p) $ do
        body' <- compileLets body
        bs' <- traverse compileInBinding bs
        case r of
            NonRec -> compileNonRecBindings r body' bs'
            Rec    -> compileRecBindings r body' bs'
    Var x n -> pure $ Var x n
    TyAbs x n k t -> TyAbs x n k <$> compileLets t
    LamAbs x n ty t -> LamAbs x n ty <$> compileLets t
    Apply x t1 t2 -> Apply x <$> compileLets t1 <*> compileLets t2
    Constant x c -> pure $ Constant x c
    Builtin x bi -> pure $ Builtin x bi
    TyInst x t ty -> TyInst x <$> compileLets t <*> pure ty
    Error x ty -> pure $ Error x ty
    IWrap x tn ty t -> IWrap x tn ty <$> compileLets t
    Unwrap x t -> Unwrap x <$> compileLets t

compileInBinding
    :: Compiling m e a
    => Binding TyName Name (Provenance a)
    -> m (Binding TyName Name (Provenance a))
compileInBinding b =  case b of
    TermBind x d rhs -> TermBind x d <$> compileLets rhs
    b@TypeBind {} -> pure b
    b@DatatypeBind {} -> pure b

compileNonRecBindings :: Compiling m e a => Recursivity -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileNonRecBindings r = foldM (compileSingleBinding r)

compileRecBindings :: Compiling m e a => Recursivity -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecBindings r body bs =
    let
        partitionBindings = partition (\case { TermBind {} -> True ; _ -> False; })
        (termBinds, typeBinds) = partitionBindings bs
    in do
        tysBound <- compileRecTypeBindings r body typeBinds
        compileRecTermBindings r tysBound termBinds

compileRecTermBindings :: Compiling m e a => Recursivity -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTermBindings _ body bs = case bs of
    [] -> pure body
    _ -> do
        binds <- forM bs $ \case
            TermBind _ vd rhs -> pure $ PIR.Def vd rhs
            _ -> ask >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
        compileRecTerms body binds

compileRecTypeBindings :: Compiling m e a => Recursivity -> PIRTerm a -> [Binding TyName Name (Provenance a)] -> m (PIRTerm a)
compileRecTypeBindings r body bs = case bs of
    []  -> pure body
    [b] -> compileSingleBinding r body b
    _   -> ask >>= \p -> throwing _Error $ UnsupportedError p "Mutually recursive datatypes"

compileSingleBinding :: Compiling m e a => Recursivity -> PIRTerm a -> Binding TyName Name (Provenance a) ->  m (PIRTerm a)
compileSingleBinding r body b =  case b of
    TermBind x d rhs -> local (const x) $ case r of
        Rec -> compileRecTerms body [PIR.Def d rhs]
        NonRec -> local (TermBinding (varDeclNameString d)) $
            PIR.mkTermLet <$> ask <*> pure (PIR.Def d rhs) <*> pure body
    TypeBind x d rhs -> local (const x) $ local (TypeBinding (tyVarDeclNameString d)) $ do
        let def = PIR.Def d rhs
        PIR.mkTypeLet <$> ask <*> pure def <*> pure body
    DatatypeBind x d -> local (const x) $ local (TypeBinding (datatypeNameString d)) $
        compileDatatype r body d
