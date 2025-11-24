{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneKindSignatures  #-}

module PlutusTx.Compiler.Utils where

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Types

import PlutusCore qualified as PLC

import GHC.Core qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Types.TyThing qualified as GHC

import Control.Monad ((<=<))
import Control.Monad.Except
import Control.Monad.Reader (MonadReader, ask)

import Language.Haskell.TH.Syntax qualified as TH

import Data.Kind qualified as Kind
import Data.Map qualified as Map
import Data.Text qualified as T

{- | Identical to `SomeTypeIn` but without existential kind. Having kind fixed to
`Type` makes it easier to pattern match and construct a different type within
universe. See how it's used in 'compileMkNil'.
-}
type SomeStarIn :: (Kind.Type -> Kind.Type) -> Kind.Type
data SomeStarIn uni = forall a. SomeStarIn !(uni (PLC.Esc a))

{-| Get the 'GHC.TyCon' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing.
-}
lookupGhcTyCon :: (Compiling uni fun m ann) => TH.Name -> m GHC.TyCon
lookupGhcTyCon thName = do
  CompileContext{ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just (GHC.ATyCon tc) -> pure tc
    _ -> throwPlain $ CompilationError $ "TyCon not found: " <> T.pack (show thName)

{-| Get the 'GHC.Name' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing.
-}
lookupGhcName :: (Compiling uni fun m ann) => TH.Name -> m GHC.Name
lookupGhcName thName = do
  CompileContext{ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just thing -> pure (GHC.getName thing)
    Nothing    -> throwPlain $ CompilationError $ "Name not found: " <> T.pack (show thName)

{-| Get the 'GHC.Id' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing.
-}
lookupGhcId :: (Compiling uni fun m ann) => TH.Name -> m GHC.Id
lookupGhcId thName = do
  CompileContext{ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just (GHC.AnId ghcId) -> pure ghcId
    _ -> throwPlain $ CompilationError $ "Id not found: " <> T.pack (show thName)

sdToStr :: (MonadReader (CompileContext uni fun) m) => GHC.SDoc -> m String
sdToStr sd = do
  CompileContext{ccFlags = flags} <- ask
  pure $ GHC.showSDocForUser flags GHC.emptyUnitState GHC.alwaysQualify sd

sdToTxt :: (MonadReader (CompileContext uni fun) m) => GHC.SDoc -> m T.Text
sdToTxt = fmap T.pack . sdToStr

throwSd
  :: (MonadError (CompileError uni fun ann) m, MonadReader (CompileContext uni fun) m)
  => (T.Text -> Error uni fun ann)
  -> GHC.SDoc
  -> m a
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
    tyConsOfExpr scrut
      <> tyConsOfBndr bndr
      <> GHC.tyConsOfType ty
      <> foldMap tyConsOfAlt alts
  GHC.Let bind body -> tyConsOfBind bind <> tyConsOfExpr body

tyConsOfBndr :: GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBndr = GHC.tyConsOfType . GHC.varType

tyConsOfBind :: GHC.Bind GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBind = \case
  GHC.NonRec bndr rhs -> binderTyCons bndr rhs
  GHC.Rec bndrs -> foldMap (uncurry binderTyCons) bndrs
 where
  binderTyCons bndr rhs = tyConsOfBndr bndr <> tyConsOfExpr rhs

tyConsOfAlt :: GHC.CoreAlt -> GHC.UniqSet GHC.TyCon
tyConsOfAlt (GHC.Alt _ vars e) = foldMap tyConsOfBndr vars <> tyConsOfExpr e
