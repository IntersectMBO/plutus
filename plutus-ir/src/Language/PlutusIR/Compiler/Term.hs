{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR terms into PLC.
module Language.PlutusIR.Compiler.Term (compileTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types

import           Control.Monad
import           Control.Monad.Except

import qualified Language.PlutusCore                  as PLC
import qualified Language.PlutusCore.MkPlc            as PLC

import           Data.List

-- | Compile a 'Term' into a PLC Term. Note: the result does *not* have globally unique names.
compileTerm :: Compiling m => Term TyName Name () -> m (PLC.Term TyName Name ())
compileTerm = \case
    Let _ r bs body -> do
        body' <- compileTerm body
        case r of
            NonRec -> compileNonRecBindings r body' ( unBl bs)
            Rec    -> compileRecBindings r body' ( unBl bs)
    Var _ n -> pure $ PLC.Var () n
    TyAbs _ n k t -> PLC.TyAbs () n k <$> compileTerm t
    LamAbs _ n ty t -> PLC.LamAbs () n ty <$> compileTerm t
    Apply _ t1 t2 -> PLC.Apply () <$> compileTerm t1 <*> compileTerm t2
    Constant _ c -> pure $ PLC.Constant () c
    TyInst _ t ty -> PLC.TyInst () <$> compileTerm t <*> pure ty
    Error _ ty -> pure $ PLC.Error () ty
    Wrap _ tn ty t -> PLC.Wrap () tn ty <$> compileTerm t
    Unwrap _ t -> PLC.Unwrap () <$> compileTerm t

compileNonRecBindings :: Compiling m => Recursivity -> PLC.Term TyName Name () -> [Binding TyName Name ()] -> m (PLC.Term TyName Name ())
compileNonRecBindings r body bs = foldM (compileSingleBinding r) body bs

compileRecBindings :: Compiling m => Recursivity -> PLC.Term TyName Name () -> [Binding TyName Name ()] -> m (PLC.Term TyName Name ())
compileRecBindings r body bs =
    let
        partitionBindings = partition (\case { TermBind {} -> True ; _ -> False; })
        (termBinds, typeBinds) = partitionBindings bs
    in do
        tysBound <- compileRecTypeBindings r body typeBinds
        compileRecTermBindings r tysBound termBinds

compileRecTermBindings :: Compiling m => Recursivity -> PLC.Term TyName Name () -> [Binding TyName Name ()] -> m (PLC.Term TyName Name ())
compileRecTermBindings _ body bs = case bs of
    [] -> pure body
    _ -> do
        binds <- forM bs $ \case
            TermBind () vd rhs -> pure $ PLC.Def vd rhs
            _ -> throwError $ CompilationError "Internal error: type binding in term binding group"
        compileRecTerms body binds

compileRecTypeBindings :: Compiling m => Recursivity -> PLC.Term TyName Name () -> [Binding TyName Name ()] -> m (PLC.Term TyName Name ())
compileRecTypeBindings r body bs = case bs of
    []  -> pure body
    [b] -> compileSingleBinding r body b
    _   -> throwError $ UnsupportedError "Mutually recursive types are not supported"

compileSingleBinding :: Compiling m => Recursivity -> PLC.Term TyName Name () -> Binding TyName Name () ->  m (PLC.Term TyName Name ())
compileSingleBinding r body b = case b of
    TermBind () d rhs -> case r of
        Rec -> compileRecTerms body [PLC.Def d rhs]
        NonRec -> do
            def <- PLC.Def d <$> compileTerm rhs
            pure $ PLC.mkTermLet () def body
    TypeBind () d rhs -> do
        let def = PLC.Def d rhs
        pure $ PLC.mkTypeLet () def body
    DatatypeBind () d -> compileDatatype r body d
