{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Core.Instance.Scoping () where

import PlutusPrelude

import UntypedPlutusCore.Core.Type

import PlutusCore.Check.Scoping
import PlutusCore.Name.Unique
import PlutusCore.Quote

import Data.Proxy
import Data.Vector qualified as Vector

firstBound :: Term name uni fun ann -> [name]
firstBound (Apply _ (LamAbs _ name body) _) = name : firstBound body
firstBound _ = []

instance name ~ Name => Reference Name (Term name uni fun) where
  referenceVia reg name term = Apply NotAName term $ Var (reg name) name

instance name ~ Name => EstablishScoping (Term name uni fun) where
  establishScoping (LamAbs _ nameDup body) = do
    name <- freshenName nameDup
    establishScopingBinder (\ann name' _ -> LamAbs ann name') name Proxy body
  establishScoping (Delay _ body) = Delay NotAName <$> establishScoping body
  establishScoping (Apply _ fun arg) =
    Apply NotAName <$> establishScoping fun <*> establishScoping arg
  establishScoping (Error _) = pure $ Error NotAName
  establishScoping (Force _ term) = Force NotAName <$> establishScoping term
  establishScoping (Var _ nameDup) = do
    name <- freshenName nameDup
    pure $ Var (registerFree name) name
  establishScoping (Constant _ con) = pure $ Constant NotAName con
  establishScoping (Builtin _ bi) = pure $ Builtin NotAName bi
  establishScoping (Constr _ i es) = Constr NotAName <$> pure i <*> traverse establishScoping es
  establishScoping (Case _ a es) = do
    esScoped <- traverse establishScoping es
    let esScopedPoked = addTheRest . map (\e -> (e, firstBound e)) $ Vector.toList esScoped
        branchBounds = map (snd . fst) esScopedPoked
        referenceInBranch ((branch, _), others) = referenceOutOfScope (map snd others) branch
    aScoped <- establishScoping a
    -- For each of the branches reference (as out-of-scope) the variables bound in that branch
    -- in all the other ones, as well as outside of the whole case-expression. This is to check
    -- that none of the transformations leak variables outside of the branch they're bound in.
    pure . referenceOutOfScope branchBounds $
      Case NotAName aScoped . Vector.fromList $
        map referenceInBranch esScopedPoked

instance name ~ Name => EstablishScoping (Program name uni fun) where
  establishScoping (Program _ ver term) = Program NotAName ver <$> establishScoping term

instance name ~ Name => CollectScopeInfo (Term name uni fun) where
  collectScopeInfo (LamAbs ann name body) = handleSname ann name <> collectScopeInfo body
  collectScopeInfo (Delay _ body) = collectScopeInfo body
  collectScopeInfo (Apply _ fun arg) = collectScopeInfo fun <> collectScopeInfo arg
  collectScopeInfo (Error _) = mempty
  collectScopeInfo (Force _ term) = collectScopeInfo term
  collectScopeInfo (Var ann name) = handleSname ann name
  collectScopeInfo (Constant _ _) = mempty
  collectScopeInfo (Builtin _ _) = mempty
  collectScopeInfo (Constr _ _ es) = foldMap collectScopeInfo es
  collectScopeInfo (Case _ arg cs) = collectScopeInfo arg <> foldMap collectScopeInfo cs

instance name ~ Name => CollectScopeInfo (Program name uni fun) where
  collectScopeInfo (Program _ _ term) = collectScopeInfo term
