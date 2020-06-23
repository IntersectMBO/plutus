{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

module Language.PlutusCore.Constant.Embed
    ( embedStaticBuiltinNameInTerm
    , embedTypedBuiltinNameInTerm
    , embedDynamicBuiltinNameInTerm
    )
where

import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

import           Data.Text                             (pack)

{- | Since built-in names don't make sense on their own, we produce a
   term which wraps the name in a sequence of abstractions and lambdas
   and then applies the name to the relevant types and variables. This
   isn't ideal, but it does what's required for testing.
-}
-- Note that we
embedBuiltinNameInTerm :: TypeScheme uni args res -> BuiltinName -> Term TyName Name uni ()
embedBuiltinNameInTerm scheme name =
    let mkVarDecl :: (Type TyName uni (), Integer) -> Quote (VarDecl TyName Name uni ())
        mkVarDecl (ty, idx) = do
          u <- freshUnique
          let argname = Name (pack $ "arg" ++ show idx) u
          -- Append an index to the arument name so we don't get "f arg arg arg"
          pure $ VarDecl () argname ty
        mkTyVarDecl :: TyName -> TyVarDecl TyName ()
        mkTyVarDecl tyname = TyVarDecl () tyname (Type ())
    in case typeComponentsOfTypeScheme scheme of
      Nothing -> Prelude.error $ "Malformed type scheme for " ++ show name ++ " in embedBuiltinNameInTerm"
      -- FIXME: we should really have a proper error here, but that involves running a *lot* of stuff in a monad
      Just (TypeComponents tynames types _) ->
          runQuote $ do
            varDecls <- mapM mkVarDecl (zip types [1..])
            -- For each argument type, generate a VarDecl for a variable of that type
            let termArgs = map (Var () . varDeclName) varDecls
                tyArgs = map (TyVar ()) tynames
                tyVarDecls = map mkTyVarDecl tynames
            pure $ mkIterTyAbs tyVarDecls (mkIterLamAbs varDecls (ApplyBuiltin () name tyArgs termArgs))

{- FIMXE: mpj: It's not clear to me that this is safe, depending on
where we run this. I'd have thought we need this to run in
MonadQuote...

@effectfully
effectfully yesterday •
Member

The resulting term is supposed to be closed, right? In that case we
don't need MonadQuote (e.g. we call runQuote everywhere in stdlib,
examples etc). Global uniqueness does not get preserved this way, but
it's just like in typeSchemeToType -- we ensure global uniqueness in
the type checker by calling normalizeType (or liftDupable sometimes).
-}


embedTypedBuiltinNameInTerm :: TypedBuiltinName uni args r -> Term TyName Name uni ()
embedTypedBuiltinNameInTerm (TypedBuiltinName sbn sch) = embedBuiltinNameInTerm  sch $ StaticBuiltinName sbn

embedStaticBuiltinNameInTerm :: (GShow uni, GEq uni, DefaultUni <: uni) => StaticBuiltinName -> Term TyName Name uni ()
embedStaticBuiltinNameInTerm sbn = withTypedBuiltinName sbn embedTypedBuiltinNameInTerm

embedDynamicBuiltinNameInTerm :: TypeScheme uni args res -> DynamicBuiltinName -> Term TyName Name uni ()
embedDynamicBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . DynBuiltinName

