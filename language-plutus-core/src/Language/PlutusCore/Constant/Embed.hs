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
-- Note that we generate fresh `Unique`s in mkVarDecl, which is called
-- via `runQuote`.  This may produce variables whose `Unique` clashes
-- with one in the surrounding code, but this is safe.  We're
-- producing closed terms like `\x -> \y -> someBuiltin x y`, and the
-- new variables disappear immediately upon application.
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

embedTypedBuiltinNameInTerm :: TypedBuiltinName uni args r -> Term TyName Name uni ()
embedTypedBuiltinNameInTerm (TypedBuiltinName sbn sch) = embedBuiltinNameInTerm  sch $ StaticBuiltinName sbn

embedStaticBuiltinNameInTerm :: (GShow uni, GEq uni, DefaultUni <: uni) => StaticBuiltinName -> Term TyName Name uni ()
embedStaticBuiltinNameInTerm sbn = withTypedBuiltinName sbn embedTypedBuiltinNameInTerm

embedDynamicBuiltinNameInTerm :: TypeScheme uni args res -> DynamicBuiltinName -> Term TyName Name uni ()
embedDynamicBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . DynBuiltinName

