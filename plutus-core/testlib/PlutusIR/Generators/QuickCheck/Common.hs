-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

module PlutusIR.Generators.QuickCheck.Common where

import PlutusPrelude

import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.Substitutions
import PlutusCore.Generators.QuickCheck.Unification

import PlutusCore.Default
import PlutusCore.Error qualified as PLC
import PlutusCore.Name.Unique
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Rename
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Error
import PlutusIR.Subst
import PlutusIR.TypeCheck

import Control.Monad.Except
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set.Lens (setOf)

-- | Compute the datatype declarations that escape from a term.
datatypes
  :: Term TyName Name DefaultUni DefaultFun ()
  -> [(TyName, (Kind ()))]
datatypes tm = case tm of
  Var _ _ -> mempty
  Builtin _ _ -> mempty
  Constant _ _ -> mempty
  Apply _ _ _ -> mempty
  LamAbs _ _ _ tm' -> datatypes tm'
  TyAbs _ _ _ tm' -> datatypes tm'
  TyInst _ _ _ -> mempty
  Let _ _ binds tm' -> foldr addDatatype (datatypes tm') binds
    where
      addDatatype (DatatypeBind _ (Datatype _ (TyVarDecl _ a k) _ _ _)) = ((a, k) :)
      addDatatype _ = id
  Error _ _ -> mempty
  _ -> error "nope"

{-| Try to infer the type of an expression in a given type and term context.
NOTE: one can't just use out-of-the-box type inference here because the
`inferType` algorithm happy renames things. -}
inferTypeInContext
  :: TypeCtx
  -> Map Name (Type TyName DefaultUni ())
  -> Term TyName Name DefaultUni DefaultFun ()
  -> Either String (Type TyName DefaultUni ())
inferTypeInContext tyctx ctx tm0 = first display $
  runQuoteT @(Either (Error DefaultUni DefaultFun ())) $ do
    -- CODE REVIEW: this algorithm is fragile, it relies on knowing that `inferType`
    -- does renaming to compute the `esc` substitution for datatypes. However, there is also
    -- not any other way to do this in a way that makes type inference actually useful - you
    -- want to do type inference in non-top-level contexts. Ideally I think type inference
    -- probably shouldn't do renaming of datatypes... Or alternatively we need to ensure that
    -- the renaming behaviour of type inference is documented and maintained.
    cfg <- modifyError (PLCError . PLC.TypeErrorE) $ getDefTypeCheckConfig ()
    -- Infer the type of `tm` by adding the contexts as (type and term) lambdas
    Normalized _ty' <- inferType cfg tm'
    -- Substitute the free variables and escaping datatypes to get back to the un-renamed type.
    let ty' = substEscape (Map.keysSet esc <> foldr (<>) (setOf ftvTy _ty') (setOf ftvTy <$> esc)) esc _ty' -- yuck
    -- Get rid of the stuff we had to add for the context.
    return $ stripFuns tms $ stripForalls mempty tys ty'
  where
    tm' = addTyLams tys $ addLams tms tm0
    rntm = case runQuoteT $ rename tm' of
      Left _ -> error "impossible"
      Right tm'' -> tm''

    -- Compute the substitution that takes datatypes that escape
    -- the scope in the inferred type (given by computing them from the
    -- renamed term) and turns them into datatypes in the old type.
    esc = Map.fromList (zip dats' $ map (TyVar ()) dats)

    dats' = map fst $ datatypes rntm
    dats = map fst $ datatypes tm'

    tys = Map.toList tyctx
    tms = Map.toList ctx

    addTyLams [] tm = tm
    addTyLams ((x, k) : xs) tm = TyAbs () x k $ addTyLams xs tm

    addLams [] tm = tm
    addLams ((x, ty) : xs) tm = LamAbs () x ty $ addLams xs tm

    stripForalls sub [] ty = substTypeParallel sub ty
    stripForalls sub ((x, _) : xs) (TyForall _ y _ b) = stripForalls (Map.insert y (TyVar () x) sub) xs b
    stripForalls _ _ _ = error "stripForalls"

    stripFuns [] ty = ty
    stripFuns (_ : xs) (TyFun _ _ b) = stripFuns xs b
    stripFuns _ _ = error "stripFuns"

typeCheckTerm
  :: Term TyName Name DefaultUni DefaultFun ()
  -> Type TyName DefaultUni ()
  -> Either String ()
typeCheckTerm = typeCheckTermInContext Map.empty Map.empty

typeCheckTermInContext
  :: TypeCtx
  -> Map Name (Type TyName DefaultUni ())
  -> Term TyName Name DefaultUni DefaultFun ()
  -> Type TyName DefaultUni ()
  -> Either String ()
typeCheckTermInContext tyctx ctx tm ty = void $ do
  ty' <- inferTypeInContext tyctx ctx tm
  unifyType tyctx mempty ty' ty
