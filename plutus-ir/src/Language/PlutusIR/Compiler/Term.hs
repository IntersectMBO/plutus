{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR terms into PLC.
module Language.PlutusIR.Compiler.Term (compileTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Reader

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC

import           Data.List

-- | Compile a 'Term' into a PLC Term. Note: the result does *not* have globally unique names.
compileTerm :: Compiling m e a => PIRTerm a -> m (PLCTerm a)
compileTerm = \case
    Let p r bs body -> local (const $ LetBinding r p) $ do
        body' <- compileTerm body
        case r of
            NonRec -> compileNonRecBindings r body' bs
            Rec    -> compileRecBindings r body' bs
    Var x n -> pure $ PLC.Var x n
    TyAbs x n k t -> PLC.TyAbs x n k <$> compileTerm t
    LamAbs x n ty t -> PLC.LamAbs x n ty <$> compileTerm t
    Apply x t1 t2 -> PLC.Apply x <$> compileTerm t1 <*> compileTerm t2
    Constant x c -> pure $ PLC.Constant x c
    Builtin x bi -> pure $ PLC.Builtin x bi
    TyInst x t ty -> PLC.TyInst x <$> compileTerm t <*> pure ty
    Error x ty -> pure $ PLC.Error x ty
    IWrap x tn ty t -> PLC.IWrap x tn ty <$> compileTerm t
    Unwrap x t -> PLC.Unwrap x <$> compileTerm t

compileNonRecBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileNonRecBindings r = foldM (compileSingleBinding r)

compileRecBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecBindings r body bs =
    let
        partitionBindings = partition (\case { TermBind {} -> True ; _ -> False; })
        (termBinds, typeBinds) = partitionBindings bs
    in do
        tysBound <- compileRecTypeBindings r body typeBinds
        compileRecTermBindings r tysBound termBinds

compileRecTermBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecTermBindings _ body bs = case bs of
    [] -> pure body
    _ -> do
        binds <- forM bs $ \case
            TermBind _ vd rhs -> pure $ PLC.Def vd rhs
            _ -> ask >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
        compileRecTerms body binds

compileRecTypeBindings :: Compiling m e a => Recursivity -> PLCTerm a -> [Binding TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecTypeBindings r body bs = case bs of
    []  -> pure body
    [b] -> compileSingleBinding r body b
    _   -> ask >>= \p -> throwing _Error $ UnsupportedError p "Mutually recursive datatypes"

compileSingleBinding :: Compiling m e a => Recursivity -> PLCTerm a -> Binding TyName Name (Provenance a) ->  m (PLCTerm a)
compileSingleBinding r body b =  case b of
    TermBind x d rhs -> local (const x) $ case r of
        Rec -> compileRecTerms body [PLC.Def d rhs]
        NonRec -> local (TermBinding (varDeclNameString d)) $ do
            def <- PLC.Def d <$> compileTerm rhs
            PLC.mkTermLet <$> ask <*> pure def <*> pure body
    TypeBind x d rhs -> local (const x) $ local (TypeBinding (tyVarDeclNameString d)) $ do
        let def = PLC.Def d rhs
        PLC.mkTypeLet <$> ask <*> pure def <*> pure body
    DatatypeBind x d -> local (const x) $ local (TypeBinding (datatypeNameString d)) $
        compileDatatype r body d
