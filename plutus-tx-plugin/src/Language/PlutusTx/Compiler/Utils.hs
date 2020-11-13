{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Language.PlutusTx.Compiler.Utils where

import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Types

import qualified CoreSyn                          as GHC
import qualified GhcPlugins                       as GHC

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Text                        as T

sdToTxt :: MonadReader (CompileContext uni fun) m => GHC.SDoc -> m T.Text
sdToTxt sd = do
  CompileContext { ccFlags=flags } <- ask
  pure $ T.pack $ GHC.showSDocForUser flags GHC.alwaysQualify sd

throwSd :: (MonadError (CompileError uni fun) m, MonadReader (CompileContext uni fun) m) => (T.Text -> Error uni fun ()) -> GHC.SDoc -> m a
throwSd constr = (throwPlain . constr) <=< sdToTxt

tyConsOfExpr :: GHC.CoreExpr -> GHC.UniqSet GHC.TyCon
tyConsOfExpr = \case
    GHC.Type ty -> GHC.tyConsOfType ty
    GHC.Coercion co -> GHC.tyConsOfType $ GHC.mkCoercionTy co
    GHC.Var v -> GHC.tyConsOfType (GHC.varType v)
    GHC.Lit _ -> mempty
    -- ignore anything in the ann
    GHC.Tick _ e -> tyConsOfExpr e
    GHC.App e1 e2 -> tyConsOfExpr e1 <> tyConsOfExpr e2
    GHC.Lam bndr e -> tyConsOfBndr bndr <> tyConsOfExpr e
    GHC.Cast e co -> tyConsOfExpr e <> GHC.tyConsOfType (GHC.mkCoercionTy co)
    GHC.Case scrut bndr ty alts ->
        tyConsOfExpr scrut <>
        tyConsOfBndr bndr <>
        GHC.tyConsOfType ty <>
        foldMap tyConsOfAlt alts
    GHC.Let bind body -> tyConsOfBind bind <> tyConsOfExpr body

tyConsOfBndr :: GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBndr = GHC.tyConsOfType . GHC.varType

tyConsOfBind :: GHC.Bind GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBind = \case
    GHC.NonRec bndr rhs -> binderTyCons bndr rhs
    GHC.Rec bndrs       -> foldMap (uncurry binderTyCons) bndrs
    where
        binderTyCons bndr rhs = tyConsOfBndr bndr <> tyConsOfExpr rhs

tyConsOfAlt :: GHC.CoreAlt -> GHC.UniqSet GHC.TyCon
tyConsOfAlt (_, vars, e) = foldMap tyConsOfBndr vars <> tyConsOfExpr e
